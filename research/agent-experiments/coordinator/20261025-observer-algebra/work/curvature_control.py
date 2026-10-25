"""Exact divided-difference curvature and local recombination controls."""
from pathlib import Path
from itertools import product
import json
root=Path(__file__).resolve().parent
def F(l,c,r):return l^(c|r)
def lin(a,b,h):return h[0]^((1^b[2])*h[1])^((1^a[1])*h[2])
checks=0;counter=None
for vals in product(range(2),repeat=9):
    a,b,h=[vals[i:i+3] for i in (0,3,6)]
    delta=[x^y for x,y in zip(a,b)]
    c=[x^y for x,y in zip(a,h)]
    error=F(*c)^F(*a)^lin(a,b,h)
    curvature=h[1]*(delta[2]^h[2])
    assert error==curvature
    checks+=1
    if error and counter is None:counter={'A':a,'B':b,'h':h,'curvature':curvature}
    # Under support inclusion and adjacent wedge vanishing, recombination is
    # physical for THIS step. Those hypotheses must be re-established later.
    subset=all(x<=d for x,d in zip(h,delta))
    wedges=[delta[i+1]*h[i]^delta[i]*h[i+1] for i in range(2)]
    if subset and not any(wedges):assert error==0
escape=None
for vals in product(range(2),repeat=15):
    a,b,h=[vals[i:i+5] for i in (0,5,10)]
    d=[x^y for x,y in zip(a,b)]
    if any(x>y for x,y in zip(h,d)):continue
    if any(d[i+1]*h[i]^d[i]*h[i+1] for i in range(4)):continue
    an=[F(*a[i:i+3]) for i in range(3)]
    bn=[F(*b[i:i+3]) for i in range(3)]
    hn=[lin(a[i:i+3],b[i:i+3],h[i:i+3]) for i in range(3)]
    dn=[x^y for x,y in zip(an,bn)]
    if any(dn[i+1]*hn[i]^dn[i]*hn[i+1] for i in range(2)):continue
    if hn[1] and not dn[1]:
        escape={'A':a,'B':b,'h':h,'delta':d,'next_A':an,'next_B':bn,
                'next_h':hn,'next_delta':dn,
                'scope':'Support inclusion is not a one-step invariant even with wedge zero before and after on these windows.'}
        break
out={'local_curvature_identity_checks':checks,'curvature_counterexample':counter,
     'support_escape':escape,'Lean_verified':False,'full_problem_solved':False}
(root/'curvature-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
