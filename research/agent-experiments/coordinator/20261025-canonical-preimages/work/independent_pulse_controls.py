"""Independent scalar evolution and exhaustive small preimage controls.

These are computational controls, never Lean proof premises.
"""
from pathlib import Path
import json,time,itertools
from backward_fields import Canonical
root=Path(__file__).resolve().parent
started=time.monotonic()
records=json.loads((root/'dyadic-pulse-checked.json').read_text())['records']
def step(s):
    if not s:return set()
    return {p for p in range(min(s)-1,max(s)+2)
            if ((p-1 in s) != ((p in s) or (p+1 in s)))}
rows=[{0}]
for _ in range(128):rows.append(step(rows[-1]))
packed=Canonical(128)
bit_controls=0
for t,s in enumerate(rows):
    for p in range(-t-2,t+3):
        assert (p in s)==bool(packed.bit(t,p));bit_controls+=1
mode_controls=0
for record in records:
    if record['U']>64:continue
    U=record['U'];mode={U};failure=None
    for t in range(65):
        A=rows[U+t];B=rows[1+t]
        delta=A^B
        if failure is None:
            bad=any(((p+1 in delta) and (p in mode)) !=
                    ((p in delta) and (p+1 in mode))
                    for p in range(U-t-1,U+t+1))
            if bad:failure=t
        mode_controls+=1
        if t<64:
            mode={p for p in range(U-t-1,U+t+2)
                  if ((p-1 in mode) ^ ((p in mode) and (p+1 not in B)) ^
                      ((p+1 in mode) and (p not in A)))}
    assert failure==record['first_W_failure_through_cap']
preimage_tests=0;negative_control=0
for U in range(2,9):
    positions=list(range(-3,U+3));target={-1,0,1,U}
    for mask in range(1<<len(positions)):
        s={p for i,p in enumerate(positions) if mask>>i&1}
        assert step(s)!=target;preimage_tests+=1
    # Removing the extra pulse restores the known seed predecessor.
    assert step({0})=={-1,0,1};negative_control+=1
# Independently exhaust the local implication used by the Lean proof.
local_controls=0
for ac,ar,bc,br,hl,hc,hr,bl in itertools.product([0,1],repeat=8):
    subset=(hr & (ar^br))==hr
    common=((ar^br)&hc)==((ac^bc)&hr)
    if subset and common:
        d=hl^((1^br)&hc)^((1^ac)&hr)
        assert ((bl^hl)^((bc^hc)|(br^hr)))==((bl^(bc|br))^d)
    local_controls+=1
out={'pass':True,'computational_controls_only':True,'Lean_proof_premise':False,
     'scalar_canonical_cells':bit_controls,'scalar_mode_timesteps':mode_controls,
     'exhaustive_small_preimages':preimage_tests,'known_seed_controls':negative_control,
     'local_truth_assignments':local_controls,'seconds':time.monotonic()-started}
(root/'independent-pulse-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
