"""Audit only the supplied six-cycle transient, with no search or synthesis."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
source=ROOT.parent/'root-clock-review/published/work/dependencies/Rule30CommonPastResearch.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3'
(ROOT/'Rule30CommonPastResearch.frozen.lean').write_bytes(source.read_bytes())
RULE={(0,0,0):0,(0,0,1):1,(0,1,0):1,(0,1,1):1,(1,0,0):1,(1,0,1):0,(1,1,0):0,(1,1,1):0}
def decode(x):return tuple((x>>j)&1 for j in range(6))
def encode(x):return sum(bit<<j for j,bit in enumerate(x))
def actual_periodic(row):return tuple(RULE[(row[j],row[(j-1)%6],row[(j-2)%6])] for j in range(6))
def mode_periodic(a,b,h):
    return tuple(h[j] ^ ((1-b[(j-2)%6]) & h[(j-1)%6]) ^ ((1-a[(j-1)%6]) & h[(j-2)%6]) for j in range(6))
def common(a,b,h,j,wrap=True):
    nxt=(j+1)%len(a) if wrap else j+1
    return ((a[j]^b[j]) & h[nxt])==(h[j] & (a[nxt]^b[nxt]))
def sub(a,b,h,j):return (h[j] & (a[j]^b[j]))==h[j]
As=[58,5,27,36,63,0];Bs=[23,40,27,36,63,0];Hs=[12,12,36,36,63,63]
states=[tuple(map(decode,values)) for values in zip(As,Bs,Hs)]
checks=[]
for t,(a,b,h) in enumerate(states):
    expected=states[t+1] if t+1<len(states) else states[-1]
    assert (actual_periodic(a),actual_periodic(b),mode_periodic(a,b,h))==expected
    assert all(common(a,b,h,j) for j in range(6))
    failures=[j for j in range(6) if not sub(a,b,h,j)]
    checks.append(dict(t=t,A=As[t],B=Bs[t],H=Hs[t],difference=As[t]^Bs[t],
        common_all_six_edges=True,subset_failures=failures))
assert checks[0]['subset_failures']==checks[1]['subset_failures']==[]
assert checks[2]['subset_failures']==[2,5]
assert all(As[t]==Bs[t] for t in range(2,6))
assert states[-1]==(decode(0),decode(0),decode(63))

# Exact white-boundary comparison, solely for the stated transient.
def actual_white(row):
    z=(0,0)+tuple(row)
    return tuple(RULE[(z[j+2],z[j+1],z[j])] for j in range(len(row)))
def mode_white(a,b,h):
    aa=(0,0)+tuple(a);bb=(0,0)+tuple(b);hh=(0,0)+tuple(h)
    return tuple(hh[j+2] ^ ((1-bb[j]) & hh[j+1]) ^ ((1-aa[j+1]) & hh[j]) for j in range(len(h)))
boundary=[]
for t,(a,b,h) in enumerate(states[:-1]):
    na,nb,nh=states[t+1]
    for name,actual,expected in [('A',na,actual_white(a)),('B',nb,actual_white(b)),('H',nh,mode_white(a,b,h))]:
        bad=[j for j in (0,1) if actual[j]!=expected[j]]
        if bad:boundary.append(dict(t=t,row=name,boundary_failures=bad))
assert boundary and boundary[0]==dict(t=0,row='A',boundary_failures=[0,1])

# One explicit horizon12 white embedding verifies the exact cone scope.
# It does NOT turn interior Common into global Common.
HORIZON=12;WIDTH=2*HORIZON+7
embedded=[tuple(tuple(row[j%6] for j in range(WIDTH)) for row in states[0])]
for _ in range(HORIZON):
    a,b,h=embedded[-1];embedded.append((actual_white(a),actual_white(b),mode_white(a,b,h)))
protected=[];global_common_failures=[]
for t,(a,b,h) in enumerate(embedded):
    reference=states[min(t,5)]
    for j in range(2*t,WIDTH):
        assert (a[j],b[j],h[j])==tuple(row[j%6] for row in reference)
    assert all(common(a,b,h,j,False) for j in range(2*HORIZON,2*HORIZON+6))
    protected.append(dict(t=t,fixed_core_common=True,subset_failures=[j for j in range(24,30) if not sub(a,b,h,j)]))
    failed=[j for j in range(WIDTH-1) if not common(a,b,h,j,False)]
    if failed:global_common_failures.append(dict(t=t,indices=failed))
assert all(sub(*embedded[0],j) for j in range(WIDTH))
assert protected[2]['subset_failures']==[26,29]
assert global_common_failures[0]['t']==1 and 1 in global_common_failures[0]['indices']
out=dict(passed=True,kernel_checked=False,search_performed=False,
    frozen_definitions_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    encoding='Each integer is a six-bit spatial row, with LSB at position0. Extend bits by position modulo6. The lists are temporal states, not cyclic time words.',
    states=checks,stationary_tail=dict(A=0,B=0,H=63,starts_at=5),
    all_time_argument='The listed five transitions reach the stationary joint state(0,0,63). Thus finite verification plus induction proves the entire temporal sequence. Six residues and wrap verify every site of a bi-infinite spatially periodic strip; on Nat they verify Actual-interior and Mode-interior for j>=2, and Common for every adjacent pair.',
    failure_scope='Initial SubAt holds at every spatial position, remains true at t1, then fails at residues2 and5 at t2. A=B from t2 onward makes Common tautological; H remains nonzero. This refutes initial-only subset propagation for the interior/spatial-periodic setting.',
    white_boundary_failures=boundary,
    not_a_white_Actual='The frozen Actual and Mode definitions include special equations at0 and1. The supplied periodic trajectories violate those boundary equations, starting with A and B at t0. They are not a counterexample to the full Nat Actual+Mode+Common statement.',
    finite_white_cone_control=dict(horizon=HORIZON,width=WIDTH,fixed_protected_core=[24,29],right_neighbor_available=30,
        checks=protected,global_common_failures=global_common_failures,
        scope='The exact given periodic initial rows, repeated and evolved with genuine white missing older cells, match the periodic reference at every j>=2t. The six fixed core cells satisfy Common through12 and show subset failure at2. Common already fails near the white boundary at t1,j1. This is a local finite-horizon witness, not global all-time Common.'),
    cyclic_time_search_limit='The initial joint state never returns: the two distinct backgrounds merge at2 and become zero at5. A search imposing temporal cyclic wrap fromt0 excludes this transient mechanism.',
    excluded_claims=['No full white-boundary Actual counterexample','No FrontStable counterexample or audit','No finite-support/all-time Common counterexample','No fixed-center or prize conclusion'])
(ROOT/'audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('finite_white_cone_control','white_boundary_failures')},indent=2))
