"""Global natural-valued polynomial block energies, with exact finite checks.
This permits cross-block compensation and differs from ordinal multiset order.
Coefficients are nonnegative, so the formula is nonnegative at every run length.
No finite fit is promoted to an invariant.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib,json,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
root=Path(__file__).resolve().parent;started=time.monotonic();N=4096;P=16
def phi(a):return a^((a<<1)|(a<<2))
def runs(d):
    while d:
        lo=(d&-d).bit_length()-1;le=((d>>lo)^((d>>lo)+1)).bit_length()-1
        yield lo,le;d&=~(((1<<le)-1)<<lo)
types=list(product(range(16),[0,3],[1,2],[1,2],[0,3]));ids={v:i for i,v in enumerate(types)}
def feature(a,b,lo,le,phase):
    def pair(i):return ((a>>i)&1)|(((b>>i)&1)<<1) if i>=0 else 0
    return ids[(phase,pair(lo-1),pair(lo),pair(lo+le-1),pair(lo+le))],le
rows=[1]
for _ in range(N+P+2):rows.append(phi(rows[-1]))
records=[]
for n in range(N):
    if not all((rows[n+i]>>(n+i)&1)==(rows[n+P+i]>>(n+P+i)&1) for i in range(3)):continue
    a,b=rows[n]<<P,rows[n+P];an,bn=rows[n+2]<<P,rows[n+P+2]
    d=Counter(feature(a,b,l,le,n%16) for l,le in runs(a^b))
    d.subtract(Counter(feature(an,bn,l,le,(n+2)%16) for l,le in runs(an^bn)))
    records.append((n,{f:c for f,c in d.items() if c}))
results=[]
for degree,modulus in [(1,1),(2,1),(3,1),(2,2)]:
    dim=len(types)*modulus*(degree+1);data=[];ri=[];ci=[];integer=[]
    for i,(n,delta) in enumerate(records):
        d=Counter()
        for (ty,le),count in delta.items():
            for k in range(degree+1):d[(ty*modulus+le%modulus)*(degree+1)+k]+=count*le**k
        integer.append(d)
        for j,v in d.items():
            if v:ri.append(i);ci.append(j);data.append(v)
    A=coo_matrix((data,(ri,ci)),shape=(len(records),dim),dtype=float).tocsr()
    train=[i for i,(n,_) in enumerate(records) if n<1024];held=[i for i,(n,_) in enumerate(records) if n>=1024]
    p=linprog(np.ones(dim),A_ub=-A[train],b_ub=-np.ones(len(train)),bounds=(0,None),
              method='highs',options={'time_limit':30.})
    rec={'degree':degree,'length_modulus':modulus,'training_unique_guarded':len(train),'heldout_unique_guarded':len(held),
         'status':p.status,'message':p.message}
    if p.success:
        # A large integer scale controls rounding errors; the result is still
        # verified by Python integer arithmetic rather than the LP residual.
        scale=4*max(sum(abs(v) for v in integer[i].values()) for i in train)+1
        w=np.rint(np.maximum(p.x,0)*scale).astype(np.int64).tolist()
        train_bad=[];held_bad=[]
        for i,(n,_) in enumerate(records):
            margin=sum(int(v)*int(w[j]) for j,v in integer[i].items())
            if margin<=0:(train_bad if n<1024 else held_bad).append({'onset':n,'exact_margin':margin})
        rec.update({'integer_scale':scale,'training_exact_failures':train_bad,'heldout_exact_failures':held_bad,
                    'nonzero_weights':[{'type':types[j//(modulus*(degree+1))],
                        'length_residue':(j//(degree+1))%modulus,'power':j%(degree+1),'coefficient':v} for j,v in enumerate(w) if v]})
        assert not train_bad
    results.append(rec);print(json.dumps({k:v for k,v in rec.items() if k not in ['nonzero_weights','heldout_exact_failures']}|
        {'heldout_failure_count':len(rec.get('heldout_exact_failures',[])),'first_heldout_failures':rec.get('heldout_exact_failures',[])[:4]}),flush=True)
out={'finite_only':True,'Lean_verified':False,'lag':P,'distinct_onsets':N,'results':results,
     'scope':'Global sums of boundary/phase-conditioned nonnegative polynomial functions of run length, optionally conditioned on length parity. Cross-block credit is allowed. Exact integer training/held-out checks are finite; numerical infeasibility is not a uniform theorem.',
     'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(root/'global-block-sum-search.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
