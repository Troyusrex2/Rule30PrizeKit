"""An exact finite prefix-cycle check, with an independent coordinate control.

Finite computations only; no Lean verification is claimed. The all-time
consequence uses the stated deterministic prefix recurrence on paper.
"""
from pathlib import Path
import hashlib,json,time

root=Path(__file__).resolve().parent
started=time.monotonic()
def prefix_step(q,mask):return ((q<<2)^((q<<1)|q))&mask
def physical_step(s):
    return {x for x in range(min(s)-1,max(s)+2)
            if (int(x-1 in s) ^ (int(x in s)|int(x+1 in s)))}

# Truth-table orientation and truncation: all small prefixes, and independent
# physical single-seed rows including cells beyond their current light cone.
local=0
for width in range(1,9):
    mask=(1<<width)-1
    for q in range(1<<width):
        want=sum((((q>>(d-2))&1 if d>=2 else 0)^(((q>>(d-1))&1 if d else 0)|((q>>d)&1)))<<d for d in range(width))
        assert prefix_step(q,mask)==want
        local+=1
s={0};q=1;mask=(1<<192)-1
for t in range(97):
    assert q==sum(1<<(x+t) for x in s if x+t<192)
    q=prefix_step(q,mask);s=physical_step(s)

width=87868;mask=(1<<width)-1;entry_time=131072;q=1
for _ in range(entry_time):q=prefix_step(q,mask)
entry=q;states=[]
for _ in range(32):
    states.append(q);q=prefix_step(q,mask)
assert q==entry, 'No period32 cycle: do not infer an all-time bound'
differences=[states[i]^states[(i+16)%32] for i in range(32)]
depths=[(d&-d).bit_length()-1 for d in differences]
assert all(d==1<<(width-1) for d in differences), depths
entry_bytes=(hex(entry)+'\n').encode('ascii')
(root/'swarm-prefix-cycle-entry.hex').write_bytes(entry_bytes)
out={'finite_computation_only':True,'Lean_verified':False,'prefix_width':width,
     'entry_time':entry_time,'closed_period':32,'local_truth_table_cases':local,
     'independent_physical_rows':97,'lag16_first_difference_depths_all32_phases':depths,
     'entry_sha256':hashlib.sha256(entry_bytes).hexdigest(),
     'cycle_state_sha256':[hashlib.sha256((hex(v)+'\n').encode('ascii')).hexdigest() for v in states],
     'paper_consequence':'For every t>=entry_time+16, the original moving-left-edge comparison at lag16 has exactly depth87867. The 87868-bit prefix evolves autonomously, and all32 cycle phases differ from their lag16 partner only at bit87867.',
     'scope':'This refutes positive asymptotic agreement-depth fraction at p=16, not Rule30 Problem1; no link to the zero-boundary absorbing-prefix theorem is asserted.',
     'seconds':time.monotonic()-started}
(root/'swarm-prefix-cycle.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
