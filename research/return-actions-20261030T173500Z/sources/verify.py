from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
prior=Path('D:/MWB/Rule30/agent-inbox/r30-root-leak-proof-20261030T155634Z-v01')
assert (prior/'READY').exists()
manifest=json.loads((prior/'SHA256SUMS.json').read_text())
for path,expected in manifest.items():assert hashlib.sha256((prior/path).read_bytes()).hexdigest()==expected
for name in ['CanonicalDecoration.lean','LeakDescent.lean']:
    assert (R/name).read_bytes()==(prior/'sources'/name).read_bytes()
def G(x):return x^((x<<1)|(x<<2))
def act_state(q,x,n):
    out=0
    for j in range(n):
        b=(x>>j)&1;out|=(b^(q!=0))<<j;q=2 if b else (1 if q==2 else 0)
    return out
def act_word(w,x,n):
    for q in reversed(w):x=act_state(q,x,n)
    return x
def sec(w,b):
    out=[]
    for q in reversed(w):out.append(2 if b else (1 if q==2 else 0));b^=q!=0
    return tuple(reversed(out))
bad=(0,0,0,2,1,2,2,2)
assert sum(q!=0 for q in bad)%2==1
assert all(q!=1 or bad[(i-1)%8]==2 for i,q in enumerate(bad))
targets=[]
for x in [42,43]:
    w=bad+bad
    assert act_word(w,x,6)==x
    for j in range(6):w=sec(w,(x>>j)&1)
    targets.append(w)
assert targets[0]==targets[1]==(1,2)*8
# Independently check that the generated good8 set really closes from A8.
seen={(0,)*8};pending=list(seen)
while pending:
    w=pending.pop()
    if sum(q!=0 for q in w)%2:continue
    for b in [0,1]:
        v=sec(w,b)
        if v not in seen:seen.add(v);pending.append(v)
assert len(seen)==34 and bad not in seen
# Match the symbolic bridge to actual integer T, with arbitrary finite tails.
checks=0
for n in range(1,7):
    for P in [1,2,3,4,8]:
        for x in [1,3,21,41]:
            cfg=x&((1<<n)-1);w=[];a=cfg
            for t in range(P):
                if n==1:q=2 if a&1 else 0
                else:q=2 if (a>>(n-1))&1 else (1 if (a>>(n-2))&1 else 0)
                w.insert(0,q);a=G(a)
            for z in [0,1,5]:
                a=cfg+(z<<n)
                for t in range(P):a=G(a)
                assert act_word(w,z,12)==(a>>n)&4095
                checks+=1
# A different gate really admits a finite same-edge trapped pair.
a,b=9,15
for t in range(128):
    assert (a^b)<8 and a&1==b&1==1
    a^=(a<<2)&~(a<<1);b^=(b<<2)&~(b<<1)
out=dict(previous_packet_hashes_verified=len(manifest),prior_sources_unchanged=True,
    return_tail_mapping_controls=checks,bad_boundary=list(bad),bad_prefixes=[42,43],
    merged_section=list(targets[0]),genuine_fixed_P8_closure_states=len(seen),bad_reachable=False,
    alternative_gate_same_edge_control_steps=128,alternative_gate_is_not_Rule30=True,
    no_uniform_injectivity_proof=True)
(R/'AUDIT.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(hashes=len(manifest),tail_mapping_checks=checks,closure=34,bad_reachable=False,alternative_gate_steps=128)))
