"""Independent packed and scalar controls for the finite-distance gap theorem."""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent;started=time.monotonic()
def R(l,c,r):return l^(c|r)
def evolve(a,h,L):
    return a^((a>>1)|(a>>2)), h^(h>>1)^((~(a>>1))&(h>>2))
def wedge(a,h):return ((a>>1)&h)^(a&(h>>1))
def good(a,h,p,q):return (((a>>p)&1)*((h>>q)&1))==(((a>>q)&1)*((h>>p)&1))
patterns=0;distance_checks=0;subset_checks=0;scalar_steps=0
for L in range(1,9):
    N=(L-1)//2
    for a in range(1<<L):
        for h in range(1<<L):
            patterns+=1;initial_a=a;initial_h=h
            aa=[a];hh=[h]
            for t in range(N):
                a,h=evolve(a,h,L)
                aa.append(a);hh.append(h)
            if patterns%127==0:
                x=[(initial_a>>i)&1 for i in range(L+2)]
                y=[(initial_h>>i)&1 for i in range(L+2)]
                for t in range(N+1):
                    assert sum(x[i]<<i for i in range(L))==aa[t]
                    assert sum(y[i]<<i for i in range(L))==hh[t]
                    x,y=([R(x[i],x[i+1],x[i+2]) for i in range(L)]+[0,0],
                         [y[i]^y[i+1]^((1^x[i+1])*y[i+2]) for i in range(L)]+[0,0])
                    scalar_steps+=1
            for cap in range(N+1):
                if any(wedge(aa[t],hh[t]) for t in range(cap+1)):break
                for t in range(cap+1):
                    for p in range(L):
                        for q in range(p,L):
                            if ((aa[t]>>q)&1) and t+(q-p)//2<=cap:
                                assert good(aa[t],hh[t],p,q)
                                distance_checks+=1
                if cap==N and not(initial_h&~initial_a):
                    assert initial_h in {0,initial_a};subset_checks+=1
# Dropping the black-right-endpoint premise breaks the finite bound.
a,h=1,12
aa=[a];hh=[h]
a,h=evolve(a,h,4);aa.append(a);hh.append(h)
assert all(not wedge(a,h) for a,h in zip(aa,hh))
assert not good(aa[0],hh[0],0,2) and not((aa[0]>>2)&1)
# One initial W layer is insufficient at distance two.
a,h=5,1
assert not wedge(a,h) and not good(a,h,0,2)
a,h=evolve(a,h,3);assert wedge(a,h)
out={'pass':True,'computational_controls_only':True,'Lean_proof_premise':False,
     'initial_pairs':patterns,'distance_implications':distance_checks,
     'initial_subset_classifications':subset_checks,'independent_scalar_timesteps':scalar_steps,
     'missing_black_endpoint_counterexample':{'A':1,'h':12,'distance':2,'common_through':1},
     'insufficient_horizon_counterexample':{'A':5,'h':1,'distance':2,'common_through':0},
     'seconds':time.monotonic()-started}
(root/'independent-gap-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
