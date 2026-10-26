"""Scalar coordinates and exhaustive arbitrary-controller escape controls.

These are independent computational controls, not Lean proof premises.
"""
from pathlib import Path
import json,random,time
root=Path(__file__).resolve().parent;started=time.monotonic();rng=random.Random(30261026)
def phi(a):return a^((a<<1)|(a<<2))
def ds(a,b,h):return h^((h<<1)&~(b<<2))^((h<<2)&~(a<<1))
def F(s):
    if not s:return set()
    return {p for p in range(min(s)-1,max(s)+2)
            if ((p-1 in s) != ((p in s) or (p+1 in s)))}
def D(a,b,h):
    if not h:return set()
    return {p for p in range(min(h)-1,max(h)+2)
            if ((p-1 in h)^((p in h) and p+1 not in b)^((p+1 in h) and p not in a))}
canon=[{0}]
for _ in range(80):canon.append(F(canon[-1]))
coordinate_steps=0
for _ in range(160):
    U=rng.randrange(1,25);V=rng.randrange(U+1);L=rng.randrange(1,20)
    h0=rng.randrange(1,1<<L);h={U-j for j in range(L) if h0>>j&1};packed=h0
    for t in range(33):
        assert all(p<=U+t for p in h)
        assert packed==sum(1<<(U+t-p) for p in h)
        a=sum(1<<(U+t-p) for p in canon[U+t])
        b=sum(1<<(U+t-p) for p in canon[V+t])
        h=D(canon[U+t],canon[V+t],h);packed=ds(a,b,packed);coordinate_steps+=1
state_controls=0;transition_controls=0;worst=[]
for L in range(1,9):
    K=(L+1)//2;states=set(range(1,1<<L));a=1;counts=[len(states)]
    for k in range(K):
        nxt=set()
        for h in states:
            for b in range(1<<max(L-1,0)):
                nh=ds(a,b,h);transition_controls+=1
                if nh<(1<<L):nxt.add(nh)
        assert 0 not in nxt
        states=nxt;counts.append(len(states));a=phi(a)
    assert not states,(L,states)
    worst.append({'L':L,'window_updates':K,'surviving_nonzero_states':counts})
    state_controls+=(1<<L)-1
# A known noncanonical older prefix DOES retain a two-cell mode.
a,b,h=3,2,1
for t in range(65):
    assert h in {1,3}
    assert ds(a,b,h)==phi(a)^phi(b)
    h=ds(a,b,h);a=phi(a);b=phi(b)
out={'pass':True,'computational_controls_only':True,'Lean_proof_premise':False,
     'physical_coordinate_D_steps':coordinate_steps,'initial_band_states':state_controls,
     'arbitrary_b_transition_controls':transition_controls,'escape_windows':worst,
     'noncanonical_escaping_control_timesteps':65,'seconds':time.monotonic()-started}
(root/'independent-escape-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
