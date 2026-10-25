"""Whole-multiset ordinal descent, with no parent-specific credit constraints.
The rank of a run is alpha(boundary,phase)*length+beta(boundary,phase).
Exact SMT handling permits ties between different block types. Finite fits
are always checked separately and do not establish a uniform theorem.
"""
from pathlib import Path
from collections import Counter
from itertools import combinations_with_replacement,product
import hashlib,json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root.parent/'new-growth-20261025T1330/solver-deps'))
import z3
started=time.monotonic();N=4096;P=16
def phi(a):return a^((a<<1)|(a<<2))
def runs(d):
    while d:
        lo=(d&-d).bit_length()-1;n=((d>>lo)^((d>>lo)+1)).bit_length()-1
        yield lo,lo+n-1;d&=~(((1<<n)-1)<<lo)
def feature(a,b,block,phase):
    lo,hi=block
    def pair(i):return ((a>>i)&1)|(((b>>i)&1)<<1) if i>=0 else 0
    return (phase,pair(lo-1),pair(lo),pair(hi),pair(hi+1)),hi-lo+1
def dm_count(old,new):
    d=Counter(old);d.subtract(new)
    nz=[(k,v) for k,v in d.items() if v]
    return bool(nz) and max(nz)[1]>0

# A separate counting implementation checks the sorted-word comparison,
# including tied ranks and zero-valued ranks.
words=[v for n in range(5) for v in combinations_with_replacement(range(4),n)]
controls=0
for old in words:
    for new in words:
        assert dm_count(old,new)==(sorted(new,reverse=True)<sorted(old,reverse=True))
        controls+=1
assert dm_count([0,0],[0]) and not dm_count([0],[0,0])
rows=[1]
for _ in range(N+P+2):rows.append(phi(rows[-1]))
records=[]
for n in range(N):
    if not all((rows[n+i]>>(n+i)&1)==(rows[n+P+i]>>(n+P+i)&1) for i in range(3)):continue
    a=rows[n]<<P;b=rows[n+P];an=rows[n+2]<<P;bn=rows[n+P+2]
    old=Counter(feature(a,b,q,n%16) for q in runs(a^b))
    new=Counter(feature(an,bn,q,(n+2)%16) for q in runs(an^bn))
    delta=old.copy();delta.subtract(new)
    records.append({'onset':n,'old':old,'new':new,'delta':{f:c for f,c in delta.items() if c}})
lookup={r['onset']:r for r in records}
types=list(product(range(16),[0,3],[1,2],[1,2],[0,3]));ids={t:i for i,t in enumerate(types)}
assert all(f[0] in ids for r in records for f in r['delta'])
training={r['onset'] for r in records if r['onset']<256}
results=[]
for iteration in range(12):
    a=[z3.Int('a'+str(i)) for i in range(len(types))];b=[z3.Int('b'+str(i)) for i in range(len(types))]
    s=z3.Solver();s.set(timeout=16000,random_seed=303025)
    for x,y in zip(a,b):s.add(x>=0,y>=0)
    def rank(f):t,n=f;return a[ids[t]]*n+b[ids[t]]
    total_pairs=0
    for n in sorted(training):
        delta=lookup[n]['delta'];features=list(delta);rs=[rank(f) for f in features]
        # Aggregate signed multiplicity for each numerical rank, so merging
        # equal ranks of distinct descriptor types is handled exactly.
        ds=[z3.Int('delta_'+str(n)+'_'+str(i)) for i in range(len(features))]
        for i,r in enumerate(rs):
            s.add(ds[i]==z3.Sum([z3.If(r==q,delta[f],0) for q,f in zip(rs,features)]))
        total_pairs+=len(features)**2
        pm=z3.IntVal(-1);nm=z3.IntVal(-1)
        for i,r in enumerate(rs):
            pnext=z3.Int('pmax_'+str(n)+'_'+str(i));nnext=z3.Int('nmax_'+str(n)+'_'+str(i))
            s.add(pnext==z3.If(z3.And(ds[i]>0,r>pm),r,pm))
            s.add(nnext==z3.If(z3.And(ds[i]<0,r>nm),r,nm));pm,nm=pnext,nnext
        s.assert_and_track(pm>nm,z3.Bool('onset_'+str(n)))
    t=time.monotonic();status=s.check()
    rec={'iteration':iteration,'training_unique_onsets':sorted(training),'solver_result':str(status),
         'solve_seconds':time.monotonic()-t,'rank_equality_pairs':total_pairs}
    if status==z3.unknown:rec['reason']=s.reason_unknown()
    elif status==z3.unsat:rec['unsat_core_onsets']=[int(str(v).removeprefix('onset_')) for v in s.unsat_core()]
    else:
        m=s.model();weights={t:(m.eval(a[i],model_completion=True).as_long(),m.eval(b[i],model_completion=True).as_long()) for i,t in enumerate(types)}
        def value(f):t,n=f;x,y=weights[t];return x*n+y
        failures=[];training_fail=[]
        for r in records:
            old=[value(f) for f,c in r['old'].items() for _ in range(c)]
            new=[value(f) for f,c in r['new'].items() for _ in range(c)]
            sorted_answer=sorted(new,reverse=True)<sorted(old,reverse=True)
            assert sorted_answer==dm_count(old,new)
            if not sorted_answer:
                failures.append(r['onset'])
                if r['onset'] in training:training_fail.append(r['onset'])
        assert not training_fail,training_fail
        rec.update({'heldout_unique_onsets':len(records)-len(training),'heldout_failures':failures,
                    'weights':[{'type':t,'alpha':x,'beta':y} for t,(x,y) in weights.items()]})
    results.append(rec)
    print(json.dumps({k:v for k,v in rec.items() if k not in ['weights','training_unique_onsets','heldout_failures']}|{'failure_count':len(rec.get('heldout_failures',[])),'first_failures':rec.get('heldout_failures',[])[:8]}),flush=True)
    if status!=z3.sat or not rec['heldout_failures']:break
    training.update(rec['heldout_failures'][:8])
    if time.monotonic()-started>225:break
out={'finite_only':True,'Lean_verified':False,'distinct_onsets':N,'guarded_onsets':len(records),'lag':P,
     'type_count':len(types),'multiset_control_pairs':controls,'solver_version':z3.get_version_string(),
     'scope':'Exact whole-multiset comparison for the stated affine block-word-length rank family; no parent credit restrictions. SAT is a finite fit, UNSAT is an unverified solver report, UNKNOWN proves nothing. No uniform rank or prize result is asserted.',
     'results':results,'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(root/'global-block-search.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
