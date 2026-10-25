"""Distinct canonical onsets, complete type table, actual global DM validation.
Earlier T,t products repeat the same pair at n=T+t; those are not independent
training/test splits. This script separates unique n ranges explicitly.
"""
from pathlib import Path
from bisect import bisect_left,bisect_right
from itertools import product
import hashlib,json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root.parent/'new-growth-20261025T1330/solver-deps'))
import z3
started=time.monotonic();N=4096;P=16
def phi(a):return a^((a<<1)|(a<<2))
def runs(d):
    out=[]
    while d:
        lo=(d&-d).bit_length()-1;n=((d>>lo)^((d>>lo)+1)).bit_length()-1
        out.append((lo,lo+n-1));d&=~(((1<<n)-1)<<lo)
    return out
def feature(a,b,block,phase):
    lo,hi=block
    def pair(i):return ((a>>i)&1)|(((b>>i)&1)<<1) if i>=0 else 0
    return (phase,pair(lo-1),pair(lo),pair(hi),pair(hi+1)),hi-lo+1
rows=[1]
for _ in range(N+P+2):rows.append(phi(rows[-1]))
records=[]
for n in range(N):
    guard=all((rows[n+i]>>(n+i)&1)==(rows[n+P+i]>>(n+P+i)&1) for i in range(3))
    if not guard:continue
    a=rows[n]<<P;b=rows[n+P];an=rows[n+2]<<P;bn=rows[n+P+2]
    old=runs(a^b);new=runs(an^bn);lo=[x[0] for x in old];hi=[x[1] for x in old]
    ps=[tuple(range(bisect_left(hi,l-4),bisect_right(lo,r))) for l,r in new]
    assert all(ps)
    rec={'onset':n,'old':[feature(a,b,v,n%16) for v in old],
         'new':[feature(an,bn,v,(n+2)%16) for v in new],'parents':ps}
    records.append(rec)
types=list(product(range(16),[0,3],[1,2],[1,2],[0,3]));ids={t:i for i,t in enumerate(types)}
assert all(f[0] in ids for rec in records for f in rec['old']+rec['new'])

def solve(train_end):
    training=[r for r in records if r['onset']<train_end];test=[r for r in records if r['onset']>=train_end]
    assert not {r['onset'] for r in training}&{r['onset'] for r in test}
    constraints={}
    for rec in training:
        children={}
        for j,ps in enumerate(rec['parents']):
            if len(ps)==1:children.setdefault(ps[0],[]).append(j)
            else:constraints[(tuple(rec['old'][k] for k in ps),rec['new'][j],'merge')]=rec['onset']
        for k,cs in children.items():
            for j in cs:constraints[(rec['old'][k],rec['new'][j],len(cs)>1)]=rec['onset']
    a=[z3.Int('a'+str(i)) for i in range(len(types))];b=[z3.Int('b'+str(i)) for i in range(len(types))]
    s=z3.Solver();s.set(timeout=30000,random_seed=303025)
    for x,y in zip(a,b):s.add(x>=0,y>=0)
    def rank(f):t,n=f;return a[ids[t]]*n+b[ids[t]]
    for i,((p,c,kind),n) in enumerate(constraints.items()):
        cond=z3.Or(*[rank(c)<=rank(v) for v in p]) if kind=='merge' else (rank(c)<rank(p) if kind else rank(c)<=rank(p))
        s.assert_and_track(cond,z3.Bool('c'+str(i)))
    result=s.check();out={'train_end_exclusive':train_end,'training_unique_onsets':len(training),'test_unique_onsets':len(test),
                        'constraints':len(constraints),'solver_result':str(result)}
    if result==z3.unknown:out['reason']=s.reason_unknown()
    elif result==z3.unsat:
        indices=[int(str(c)[1:]) for c in s.unsat_core()];items=list(constraints.items())
        out['unsat_core']=[{'constraint':items[i][0],'onset':items[i][1]} for i in indices]
    else:
        m=s.model();weights={t:(m.eval(a[i],model_completion=True).as_long(),m.eval(b[i],model_completion=True).as_long()) for i,t in enumerate(types)}
        def value(f):t,n=f;x,y=weights[t];return x*n+y
        out['weights']=[{'type':t,'alpha':x,'beta':y} for t,(x,y) in weights.items()]
        for label,rows_to_test in [('training',training),('heldout',test)]:
            stats={'global_DM_failures':0,'pure_child_failures':0,'merge_failures':0,'first_global_failure':None,'first_pure_failure':None}
            for rec in rows_to_test:
                old=list(map(value,rec['old']));new=list(map(value,rec['new']))
                if not sorted(new,reverse=True)<sorted(old,reverse=True):
                    stats['global_DM_failures']+=1
                    if stats['first_global_failure'] is None:stats['first_global_failure']={'onset':rec['onset'],'old_sorted':sorted(old,reverse=True),'new_sorted':sorted(new,reverse=True)}
                children={}
                for j,ps in enumerate(rec['parents']):
                    if len(ps)==1:children.setdefault(ps[0],[]).append(j)
                    else:stats['merge_failures']+=int(new[j]>max(old[k] for k in ps))
                for k,cs in children.items():
                    for j in cs:
                        if not(new[j]<old[k] if len(cs)>1 else new[j]<=old[k]):
                            stats['pure_child_failures']+=1
                            if stats['first_pure_failure'] is None:stats['first_pure_failure']={'onset':rec['onset'],'parent':rec['old'][k],'child':rec['new'][j],'strict':len(cs)>1}
            out[label]=stats
    return out

results=[]
for end in [256,1024,2048]:
    r=solve(end);results.append(r)
    print(json.dumps({k:v for k,v in r.items() if k not in ['weights','unsat_core']}),flush=True)
    if r['solver_result']!='sat':break
out={'finite_only':True,'Lean_verified':False,'canonical_lag':P,'distinct_onsets':N,'type_count':len(types),
     'rank_family':'R(block)=alpha(boundary type)*length+beta(boundary type); nonnegative integer coefficients; phase mod16 and one-cell halo',
     'results':results,'seconds':time.monotonic()-started,'solver_version':z3.get_version_string(),
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'SAT tables are hypotheses; UNSAT is an unverified solver report for this precise affine causal-rank template. Global DM comparison is independently evaluated, and no uniform rank is asserted.'}
(root/'block-rank-distinct-onsets.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
