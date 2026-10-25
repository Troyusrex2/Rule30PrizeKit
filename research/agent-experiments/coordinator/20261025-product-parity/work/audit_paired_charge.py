"""Independent scalar rings and low-pivot rank checks; no local flux variables."""
from pathlib import Path
import hashlib,json,time
root=Path(__file__).resolve().parent;tick=time.monotonic()
path=root/'paired-charge.json';data=json.loads(path.read_text(encoding='utf-8'))
def low_insert(basis,row):
    while row:
        p=(row&-row).bit_length()-1
        if p not in basis:basis[p]=row;return
        row^=basis[p]
def output(ring,linear=False):
    n=len(ring);new=[]
    for p in range(n):
        pair=[]
        for coordinate in range(2):
            l,c,r=[ring[q%n][coordinate] for q in [p-1,p,p+1]]
            pair.append((l!=c)!=r if linear else l!=(c or r))
        new.append(pair)
    return new
def constraint(old,new,W):
    n=len(old);row=0
    for p in range(n):
        before=after=0
        for k in range(W):
            a,b=old[(p+k)%n];x,y=new[(p+k)%n]
            before|=(int(a)+2*int(b))<<(2*k)
            after|=(int(x)+2*int(y))<<(2*k)
        row^=(1<<before)^(1<<after)
    return row
records=[];ring_count=0;linear_controls=0;rule30_charge_failures=0
for saved in data['records']:
    W=saved['width'];columns=4**W;target=columns-saved['density_space_dimension']
    density=[int(x,16) for x in saved['density_basis_hex']]
    trivial=[int(x,16) for x in saved['trivial_basis_hex']]
    ind={};tri={}
    for v in density:low_insert(ind,v)
    for v in trivial:low_insert(tri,v)
    assert len(ind)==len(density)==saved['density_space_dimension']
    assert len(tri)==len(trivial)==saved['constant_and_coboundary_dimension']
    basis={};count=0
    for N in range(1,9):
        for raw in range(1<<(2*N)):
            old=[[(raw>>p)&1,(raw>>(N+p))&1] for p in range(N)]
            new=output(old);row=constraint(old,new,W)
            assert all(not((row&v).bit_count()&1) for v in density+trivial)
            low_insert(basis,row);count+=1
            if W==1:
                linear=output(old,True)
                assert sum(v[0] for v in old)%2==sum(v[0] for v in linear)%2
                linear_controls+=1
                rule30_charge_failures+=sum(v[0] for v in old)%2!=sum(v[0] for v in new)%2
        if len(basis)==target:break
    assert len(basis)==target,(W,len(basis),target)
    ring_count+=count
    records.append({'width':W,'scalar_rings':count,'through_ring_length':N,
       'independent_constraint_rank':len(basis),'independent_density_dimension':columns-len(basis),
       'saved_bases_independent':True,'all_saved_basis_vectors_pass':True})
assert rule30_charge_failures and linear_controls
out={'finite_template_only':True,'Lean_verified':False,'full_problem_solved':False,
     'records':records,'scalar_rings':ring_count,'rule150_parity_controls':linear_controls,
     'rule30_rejects_rule150_charge':rule30_charge_failures,'all_dimensions_match':True,
     'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'seconds':time.monotonic()-tick,
     'scope':'Independent finite-ring constraints and basis/rank checks match the saved density spaces. The uniform proof, if accepted, is separate.'}
(root/'paired-independent-verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
