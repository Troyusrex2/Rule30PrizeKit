"""Exact F2 local conservation-law search for Rule30 x Rule30.

The complete local flux identity is imposed, not a sample of finite rings.
Quotient by constants and spatial coboundaries to isolate mixed pair charges.
This finite template classification does not prove an arbitrary-width result.
"""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent;tick=time.monotonic()

def rule(a,b,c):
    return ((a&1)^((b&1)|(c&1))) | ((((a>>1)&1)^(((b>>1)&1)|((c>>1)&1)))<<1)

def digits(word,n):return [(word>>(2*i))&3 for i in range(n)]
def pack(word):return sum(x<<(2*i) for i,x in enumerate(word))

def insert(basis,row):
    while row:
        p=row.bit_length()-1
        if p not in basis:basis[p]=row;return
        row^=basis[p]

def nullspace(basis,n):
    out=[]
    for f in range(n):
        if f in basis:continue
        value=1<<f
        for p,row in sorted(basis.items()):
            if (row&value).bit_count()&1:value^=1<<p
        assert all(not((row&value).bit_count()&1) for row in basis.values())
        out.append(value)
    return out

records=[]
for W in range(1,5):
    n_density=4**W;n_flux=4**(W+1);variables=n_density+n_flux
    equations=[];basis={};mask=4**(W+1)-1;rho_mask=(1<<n_density)-1
    for word in range(4**(W+2)):
        seq=digits(word,W+2)
        old=pack(seq[1:-1]);new=pack([rule(*seq[i:i+3]) for i in range(W)])
        left=word&mask;right=word>>2
        row=(1<<old)^(1<<new)^(1<<(n_density+left))^(1<<(n_density+right))
        equations.append(row);insert(basis,row)
    kernel=nullspace(basis,variables);projection={}
    for vector in kernel:insert(projection,vector&rho_mask)
    trivial={};insert(trivial,rho_mask)
    for state in range(4**(W-1)):
        values=0
        for block in range(4**W):
            left=block%(4**(W-1));right=block//4
            if (left==state)!=(right==state):values|=1<<block
        insert(trivial,values)
    assert all(not((row&v).bit_count()&1) for row in equations for v in kernel)
    quotient=[];combined=dict(trivial)
    for _,vector in sorted(projection.items()):
        old_rank=len(combined);insert(combined,vector)
        if len(combined)>old_rank:quotient.append(vector)
    record={'width':W,'density_variables':n_density,'flux_variables':n_flux,
      'complete_local_equations':len(equations),'rank':len(basis),
      'full_kernel_dimension':len(kernel),'density_space_dimension':len(projection),
      'constant_and_coboundary_dimension':len(trivial),
      'new_quotient_dimension':len(quotient),
      'density_basis_hex':[hex(v) for _,v in sorted(projection.items())],
      'trivial_basis_hex':[hex(v) for _,v in sorted(trivial.items())],
      'candidate_densities_hex':[hex(v) for v in quotient]}
    records.append(record)
    print(json.dumps({k:v for k,v in record.items() if not k.endswith('_hex')}),flush=True)
    if quotient:break
out={'finite_template_only':True,'Lean_verified':False,'full_problem_solved':False,
     'records':records,'seconds':time.monotonic()-tick,
     'scope':'Exact complete local flux identity for binary pair alphabet, density widths1..4. No arbitrary-width or canonical-only classification.'}
(root/'paired-charge.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'seconds':out['seconds'],'widths':len(records),'new_candidates':sum(r['new_quotient_dimension'] for r in records)}),flush=True)
