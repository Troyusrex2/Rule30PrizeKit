"""An all-time candidate barrier with periodic, not finite, backgrounds.

Finite checks here precede a planned Lean proof. They do not refute the
canonical finite-background observer conjecture.
"""
from pathlib import Path
import json,random
root=Path(__file__).resolve().parent;rng=random.Random(301910)
records=[]
for k in range(1,9):
    T=128;origin=3*(3*k+T+12);L=2*origin+3;mask=(1<<L)-1
    a=sum(1<<p for p in range(L) if (p-origin)%3==1)
    b=sum(1<<p for p in range(L) if (p-origin)%3==2)
    h=sum(1<<(origin+p) for p in [-3*k-2,-3*k-1,3*k+1,3*k+2])
    c=a^h;different=None;first_curvature=None;initial_h=h
    def right(v):return (v>>1)|((v&1)<<(L-1))
    def left(v):return ((v<<1)|(v>>(L-1)))&mask
    def F(v):return left(v)^(v|right(v))
    for t in range(T+1):
        assert not(h>>(origin+1)&1)
        delta=a^b
        wedge=(h&right(delta))^(delta&right(h))
        assert wedge==0,(k,t)
        if t==0:assert h&~delta==0
        if t==1:assert a==b==mask
        if t>=2:assert a==b==0
        if different is None and ((c^a)>>(origin+1)&1):different=t
        curvature=h&(right(delta)^right(h))
        if curvature and first_curvature is None:first_curvature=t
        base=left(h)^(h&~right(b))^(right(h)&~a)
        theta=rng.getrandbits(L)
        gauged=left(h)^(h&(~right(b)^(theta&right(delta))))^(right(h)&(~a^(theta&delta)))
        assert base==gauged
        a,b,h,c=F(a),F(b),base&mask,F(c)
    records.append({'k':k,'time_checked':T,'auxiliary_center_always_zero':True,
                    'all_gauge_wedges_zero':True,'first_curvature_time':first_curvature,
                    'first_actual_recombination_center_difference':different,
                    'auxiliary_initial_support':[-3*k-2,-3*k-1,3*k+1,3*k+2],
                    'backgrounds_finite_at_time_zero':False,'backgrounds_vacuum_from_time_two':True})
out={'records':records,'finite_checks_only':True,'Lean_verified':False,
     'canonical_observer_refuted':False,'full_problem_solved':False,
     'scope':'A(p)=[p%3=1], B(p)=[p%3=2] are valid infinite periodic Rule30 backgrounds. All-time claims require the separate Lean proof. They have no left edge. Do not apply this counterexample to finite or left-bounded initial backgrounds.'}
(root/'merging-backgrounds.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
