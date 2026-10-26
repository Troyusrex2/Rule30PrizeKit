"""Literal whole-period refutation certificate for a parity-only code decoder."""
from pathlib import Path
import json,sys
r=Path(__file__).resolve().parent
coordinate=int(sys.argv[1]) if len(sys.argv)>1 else 1
assert coordinate in [1,2]
def encode(z,m):
    xs=[(z>>i)&1 for i in range(m)];i=next((i for i,x in enumerate(xs) if x),m)
    return [0]+xs if i>=m-2 else xs[:i+2]+[xs[i+1]]+xs[i+2:]
rows=[encode(z,4) for z in range(16)];profiles=[]
for xs in rows:
    row=xs[:];bits=[]
    for t in range(8):
        bits.append(row[-1])
        row=[(30>>(4*x+2*(row[i-1] if i else 0)+(row[i-2] if i>=2 else 0)))&1 for i,x in enumerate(row)]
    assert row==xs
    profiles.append(bits)
basis={}
for t in range(8):
    v=sum(profiles[z][t]<<z for z in range(16))
    while v:
        p=v.bit_length()-1
        if p not in basis:basis[p]=v;break
        v^=basis[p]
target=sum(((z>>coordinate)&1)<<z for z in range(16));v=target
while v and v.bit_length()-1 in basis:v^=basis[v.bit_length()-1]
assert v
L=1<<(v.bit_length()-1)
for p,b in sorted(basis.items()):
    if (b&L).bit_count()%2:L^=1<<p
if L.bit_count()%2:L^=1 # Include all-white row to also annihilate constants.
assert all((b&L).bit_count()%2==0 for b in basis.values())
assert (target&L).bit_count()%2==1 and L.bit_count()%2==0
indices=[z for z in range(16) if (L>>z)&1]
assert all(sum(profiles[z][t] for z in indices)%2==0 for t in range(8))
out={'passed':True,'width':5,'whole_period':8,'target_code_coordinate':coordinate,
     'witness':[{'code':z,'canonical_word':rows[z],'head_period':profiles[z],'target':(z>>coordinate)&1} for z in indices],
     'xor_of_all_head_periods':[sum(profiles[z][t] for z in indices)%2 for t in range(8)],
     'xor_of_targets':1,'even_witness_size':True,
     'no_affine_parity_filter_for_this_coordinate':True,'Lean_verified':False,
     'canonical_observer_refuted':False,'full_problem_solved':False}
(r/('linear-decoder-negative-control.json' if coordinate==1 else 'penultimate-linear-negative-control.json')).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
