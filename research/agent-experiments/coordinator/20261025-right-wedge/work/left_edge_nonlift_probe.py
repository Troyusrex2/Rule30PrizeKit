"""A stronger finite-horizon family retaining the left edge and exterior phase.

This script is finite evidence only. It does not assert zero center outputs,
all-time W, or a counterexample to the canonical observer target.
"""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent;started=time.monotonic()
def F(a):return (a<<1)^(a|(a>>1))
def D(a,b,h):return (h<<1)^((~(b>>1))&h)^((~a)&(h>>1))
def W(delta,h):return ((delta>>1)&h)^(delta&(h>>1))
records=[]
for H in range(7):
    e=2*H+6;U=1<<e;K=2*H+3;V=U-K;origin=U+H+4
    needed=set(range(U-1,U+H+2))|set(range(V-1,V+H+2));rows={}
    a=1<<origin
    for t in range(U+H+2):
        if t in needed:rows[t]=a
        a=F(a)
    bit=lambda a,p:(a>>(origin+p))&1
    rho=next(d for d in range(1,2*U+1) if bit(rows[U],U-d))
    assert rho>K
    q=1<<(origin+U);h0=rows[U]^rows[V]^q
    delta0=rows[U]^rows[V]
    assert not(h0&~delta0) and bit(h0,-U)==1
    assert bit(h0,U)==0
    center=[]
    for t in range(H+1):
        a,b=rows[U+t],rows[V+t];delta=a^b;h=delta^q
        assert W(delta,h)==0
        assert not(h>>(origin+V+t+1))  # Exact right-exterior phase zero.
        assert bit(h,-U-t)==1
        center.append(bit(h,0))
        assert D(a,b,delta)==(rows[U+t+1]^rows[V+t+1])
        nq=D(a,b,q)
        assert nq==F(q)
        assert D(a,b,h)==(rows[U+t+1]^rows[V+t+1]^nq)
        q=nq
    # Any previous subset field g has g(U)=g(U+1)=0. To lift the removed
    # pulse, the unique right-boundary reconstruction is forced to be one
    # at every p from U-1 through V-1, where previous delta is zero.
    ap,bp=rows[U-1],rows[V-1]
    assert all(bit(ap,p)==1 for p in range(V-1,U))
    assert bit(bp,V-1)==1 and (bit(ap,V-1)^bit(bp,V-1))==0
    g={U:0,U+1:0}
    for p in range(U,V-1,-1):
        g[p-1]=int(p==U)^((1^bit(bp,p+1))*g[p])^((1^bit(ap,p))*g[p+1])
    assert all(g[p]==1 for p in range(V-1,U))
    records.append({'H':H,'e':e,'U':U,'V':V,'gap':K,'rho':rho,
                    'carries_canonical_left_edge':True,'right_exterior_phase_zero_through_H':True,
                    'common_W_through_H':True,'D_through_H':True,
                    'no_previous_subset_lift_local_obstruction':{'position':V-1,'forced_preimage':1,'previous_delta':0},
                    'center_observations_through_H':center,'zero_center_assumed':False})
out={'finite_evidence_only':True,'Lean_verified':False,'full_problem_solved':False,
     'all_time_common_mode_found':False,'records':records,'seconds':time.monotonic()-started}
(root/'left-edge-nonlift-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
