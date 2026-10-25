"""Exact F2 conservation with spatial and temporal clocks on paired histories.

Full local identities, with the phase-shifted zero-score space removed.
Small finite clock/width search only; no unbounded theorem is inferred.
"""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent;tick=time.monotonic()

def cell_rule(a,b,c,rule):
    value=0
    for i in range(2):
        l,m,r=(a>>i)&1,(b>>i)&1,(c>>i)&1
        bit=(l^(m|r)) if rule==30 else (l^m^r)
        value|=bit<<i
    return value
def word_digits(v,n):return [(v>>(2*i))&3 for i in range(n)]
def pack(xs):return sum(x<<(2*i) for i,x in enumerate(xs))
def insert(basis,row):
    while row:
        p=row.bit_length()-1
        if p not in basis:basis[p]=row;return
        row^=basis[p]
def reduce(basis,row):
    while row:
        p=row.bit_length()-1
        if p not in basis:return row
        row^=basis[p]
    return 0
def kernel(basis,n):
    result=[]
    for free in range(n):
        if free in basis:continue
        v=1<<free
        for p,row in sorted(basis.items()):
            if (row&v).bit_count()&1:v^=1<<p
        assert all(not((r&v).bit_count()&1) for r in basis.values())
        result.append(v)
    return result

def solve(q,r,W,rule=30):
    D=4**W;J=4**(W+1);nd=q*r*D;nf=q*r*J
    def rho(t,s,w):return ((t%r)*q+(s%q))*D+w
    def flux(t,s,w):return nd+((t%r)*q+(s%q))*J+w
    basis={};equations=[]
    for t in range(r):
        for s in range(q):
            for word in range(4**(W+2)):
                a=word_digits(word,W+2)
                before=pack(a[1:-1]);after=pack([cell_rule(*a[i:i+3],rule) for i in range(W)])
                row=(1<<rho(t+1,s,after))^(1<<rho(t,s,before))^\
                    (1<<flux(t,s,word%(4**(W+1))))^(1<<flux(t,s+1,word//4))
                equations.append(row);insert(basis,row)
    vectors=kernel(basis,nd+nf);density={};mask=(1<<nd)-1
    for v in vectors:insert(density,v&mask)
    trivial={};P=4**(W-1)
    for t in range(r):
        for s in range(q):
            for block in range(P):
                values=0
                for w in range(D):
                    # B_s can occur in rho_(s-1)'s tail and rho_s's prefix.
                    if w//4==block:values^=1<<rho(t,s-1,w)
                    if w%P==block:values^=1<<rho(t,s,w)
                insert(trivial,values)
    # One phase-supported constant shared by all times fixes the common
    # state-independent cyclic total. The other constants are gradients.
    const=0
    for t in range(r):
        for w in range(D):const|=1<<rho(t,0,w)
    insert(trivial,const)
    expected=q*r*P-r+1;assert len(trivial)==expected
    assert all(reduce(density,v)==0 for v in trivial.values())
    merged=dict(trivial);extra=[]
    for _,v in sorted(density.items()):
        before=len(merged);insert(merged,v)
        if len(merged)>before:extra.append(v)
    assert len(merged)==len(density)
    return {'q':q,'r':r,'width':W,'rule':rule,'density_variables':nd,'flux_variables':nf,
       'complete_local_equations':len(equations),'full_rank':len(basis),'full_kernel_dimension':len(vectors),
       'density_dimension':len(density),'phase_gradient_and_constant_dimension':len(trivial),
       'new_charge_dimension':len(extra),'density_basis_hex':[hex(v) for _,v in sorted(density.items())],
       'trivial_basis_hex':[hex(v) for _,v in sorted(trivial.items())],
       'candidate_densities_hex':[hex(v) for v in extra]}

records=[];stop=None
for q,r in [(2,1),(3,1),(2,2),(3,2)]:
    for W in [1,2,3]:
        if time.monotonic()-tick>210:stop='internal_time_budget';break
        result=solve(q,r,W);records.append(result)
        print(json.dumps({k:v for k,v in result.items() if not k.endswith('_hex')}),flush=True)
        if result['new_charge_dimension']:stop='candidate_found';break
    if stop:break
control=solve(1,1,1,150)
assert control['new_charge_dimension']>=2
out={'finite_template_only':True,'Lean_verified':False,'full_problem_solved':False,
    'records':records,'rule150_control':control,'stop':stop,'seconds':time.monotonic()-tick,
    'scope':'Small specified spatial/time clocks and widths only; exact phase-current equations. No classification at all clocks, all widths, or on only canonical histories.'}
(root/'clock-charge.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'records':len(records),'stop':stop,'seconds':out['seconds'],
    'rule150_extra':control['new_charge_dimension']}),flush=True)
