"""One prespecified embedding counterexample; no search."""
from pathlib import Path
import json
def D(n):return n^((n>>1)|(n>>2))
def literal(n):
    b=[(n>>i)&1 for i in range(n.bit_length()+2)]
    return sum((b[i]^(b[i+1]|b[i+2]))<<i for i in range(n.bit_length()))
def gate(n,t):return ((n&1)|((n>>1)&1)) if t%2==0 else n&1
small=[10,13,10]
large=[130,227,154,245,138,237,146,255,128]
for row in [small,large]:
    assert all(D(a)==b and literal(a)==b for a,b in zip(row,row[1:]))
assert all(gate(n,t)==1 for t,n in enumerate(small))
assert (10%8)+128*(10>>3)==130
g=[gate(n,t) for t,n in enumerate(large)]
assert g==[1,1,1,1,1,1,1,1,0]
assert D(D(10)).bit_count()==2 and D(D(130)).bit_count()==4
out={'status':'PASS; one exact analytic control',
     'embedding':'insert four whites at low-first position3',
     'safe_seed':10,'safe_two_cycle':small,'embedded_seed':130,
     'embedded_rows':large,'selected_gates':g,
     'first_failure_time':8,'macro_images':[10,154],
     'macro_black_counts':[2,4],
     'scope':'refutes this S-preservation and zero-insertion lockstep monotonicity only',
     'regularity_refuted':False,'new_lean_claim':False}
Path(__file__).with_name('CONTROL.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
