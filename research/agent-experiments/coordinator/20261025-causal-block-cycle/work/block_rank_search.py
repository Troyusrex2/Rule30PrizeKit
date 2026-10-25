"""Learn an unbounded block-size rank, then test actual global multiset descent.
This is a deliberately restricted candidate family, not a proof search result.
"""
from pathlib import Path
import hashlib,json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root.parent/'new-growth-20261025T1330/solver-deps'))
import z3
started=time.monotonic()
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
for _ in range(500):rows.append(phi(rows[-1]))
types=set();constraints={};training=[];test=[]
for T in range(96):
    a=rows[T]<<16;b=rows[T+16]
    for t in range(256):
        an=phi(phi(a));bn=phi(phi(b));old=runs(a^b);new=runs(an^bn)
        guard=all((rows[T+t+i]>>(T+t+i)&1)==(rows[T+16+t+i]>>(T+16+t+i)&1) for i in range(3))
        if guard:
            fo=[feature(a,b,v,(T+t)%16) for v in old]
            fn=[feature(an,bn,v,(T+t+2)%16) for v in new]
            ps=[tuple(k for k,(lo,hi) in enumerate(old) if lo<=nh and nl-4<=hi) for nl,nh in new]
            info={'T':T,'P':16,'time':t,'old':fo,'new':fn,'parents':ps}
            if T<32 and t<128:
                training.append(info);types.update(x[0] for x in fo+fn)
                for k,p in enumerate(fo):
                    cs=[j for j,v in enumerate(ps) if v==(k,)]
                    for j in cs:constraints[(p,fn[j],len(cs)>1)]=info
                for j,parents in enumerate(ps):
                    if len(parents)>1:
                        # A necessary condition for the child not to outrank
                        # every causal parent in a local multiset rewrite.
                        constraints[(tuple(fo[k] for k in parents),fn[j],'merge')]=info
            else:test.append(info)
        a,b=phi(a),phi(b)
types=sorted(types);ids={t:i for i,t in enumerate(types)}
alpha=[z3.Int('a'+str(i)) for i in range(len(types))];beta=[z3.Int('b'+str(i)) for i in range(len(types))]
s=z3.Solver();s.set(timeout=30000,random_seed=303025)
for a,b in zip(alpha,beta):s.add(a>=0,b>=0)
def rank(f):t,n=f;return alpha[ids[t]]*n+beta[ids[t]]
for i,((p,c,kind),info) in enumerate(constraints.items()):
    if kind=='merge':condition=z3.Or(*[rank(c)<=rank(v) for v in p])
    else:condition=rank(c)<rank(p) if kind else rank(c)<=rank(p)
    s.assert_and_track(condition,z3.Bool('constraint'+str(i)))
status=s.check();out={'finite_only':True,'Lean_verified':False,'rank_family':'R(block)=alpha(boundary type)*length+beta(boundary type), nonnegative integer coefficients; global DM order of these natural block ranks',
    'boundary_type':'time phase mod16 plus one-cell halo pair, first pair, last pair, right halo pair',
    'training_guarded_transitions':len(training),'heldout_guarded_transitions':len(test),'types':len(types),
    'deduplicated_constraints':len(constraints),'solver_result':str(status),'solver_version':z3.get_version_string()}
if status==z3.unsat:
    indices=[int(str(x).removeprefix('constraint')) for x in s.unsat_core()]
    items=list(constraints.items())
    out['unsat_core']=[{'constraint':items[i][0],'witness':items[i][1]} for i in indices]
elif status==z3.unknown:out['reason']=s.reason_unknown()
else:
    model=s.model();weights={t:(model.eval(alpha[i],model_completion=True).as_long(),model.eval(beta[i],model_completion=True).as_long()) for i,t in enumerate(types)}
    def value(f):
        t,n=f
        if t not in weights:return None
        a,b=weights[t];return a*n+b
    unseen=0;violations=[];pure_bad=0;merge_bad=0
    for rec in test:
        old=list(map(value,rec['old']));new=list(map(value,rec['new']))
        if None in old+new:unseen+=1;continue
        if not sorted(new,reverse=True)<sorted(old,reverse=True):
            if len(violations)<8:violations.append({**rec,'old_rank_sorted':sorted(old,reverse=True),'new_rank_sorted':sorted(new,reverse=True)})
        for k,p in enumerate(old):
            cs=[j for j,v in enumerate(rec['parents']) if v==(k,)]
            pure_bad+=sum(not(new[j]<p if len(cs)>1 else new[j]<=p) for j in cs)
        for j,ps in enumerate(rec['parents']):
            if len(ps)>1:merge_bad+=int(new[j]>max(old[k] for k in ps))
    out.update({'weights':[{'type':t,'alpha':a,'beta':b} for t,(a,b) in weights.items()],
                'unseen_type_transitions':unseen,'heldout_global_counterexamples_first8':violations,
                'heldout_pure_failures':pure_bad,'heldout_merge_failures':merge_bad,
                'scope':'A fitted coefficient table is not a theorem. Global DM descent is checked independently after fitting local causal constraints.'})
out['seconds']=time.monotonic()-started;out['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(root/'block-rank-search.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['unsat_core','weights','heldout_global_counterexamples_first8']}),flush=True)
