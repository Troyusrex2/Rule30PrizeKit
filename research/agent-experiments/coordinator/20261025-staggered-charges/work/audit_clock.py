"""Independent scalar cyclic configurations and low-pivot density ranks."""
from pathlib import Path
import hashlib,json,time
root=Path(__file__).resolve().parent;tick=time.monotonic()
path=root/'clock-charge.json';data=json.loads(path.read_text(encoding='utf-8'))
def put(basis,row):
    while row:
        p=(row&-row).bit_length()-1
        if p not in basis:basis[p]=row;return
        row^=basis[p]
def next_row(old,rule):
    n=len(old);result=[]
    for p in range(n):
        cells=[]
        for k in range(2):
            a,b,c=[old[j%n][k] for j in [p-1,p,p+1]]
            cells.append((a^b^c) if rule==150 else a^(b|c))
        result.append(cells)
    return result

records=[];rings=0
for saved in data['records']+[data['rule150_control']]:
    q,r,W,rule=[saved[k] for k in ['q','r','width','rule']];D=4**W;variables=q*r*D
    target=variables-saved['density_dimension'];basis={};count=0
    density=[int(v,16) for v in saved['density_basis_hex']]
    trivial=[int(v,16) for v in saved['trivial_basis_hex']]
    independent={};triv_independent={}
    for v in density:put(independent,v)
    for v in trivial:put(triv_independent,v)
    assert len(independent)==saved['density_dimension'] and len(triv_independent)==saved['phase_gradient_and_constant_dimension']
    for N in range(q,10,q):
        for raw in range(1<<(2*N)):
            old=[[(raw>>p)&1,(raw>>(N+p))&1] for p in range(N)];new=next_row(old,rule)
            old_words=[];new_words=[]
            for p in range(N):
                a=b=0
                for j in range(W):
                    x,y=old[(p+j)%N];u,v=new[(p+j)%N]
                    a|=(x+2*y)<<(2*j);b|=(u+2*v)<<(2*j)
                old_words.append(a);new_words.append(b)
            for t in range(r):
                row=0
                for p in range(N):
                    s=p%q
                    row^=(1<<((t*q+s)*D+old_words[p]))^\
                         (1<<((((t+1)%r)*q+s)*D+new_words[p]))
                assert all(not((row&v).bit_count()&1) for v in density+trivial)
                put(basis,row)
            count+=1
        if len(basis)==target:break
    assert len(basis)==target,(q,r,W,rule,len(basis),target)
    rings+=count
    records.append({'q':q,'r':r,'width':W,'rule':rule,'cyclic_states':count,
      'through_ring_length':N,'independent_constraint_rank':len(basis),
      'density_dimension':variables-len(basis),'saved_bases_independent':True,
      'all_saved_vectors_pass':True})
out={'finite_template_only':True,'Lean_verified':False,'full_problem_solved':False,
     'records':records,'cyclic_states':rings,'all_dimensions_match':True,
     'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'seconds':time.monotonic()-tick,
     'scope':'Independent scalar periodic rings, at lengths divisible by the spatial clock, validate the specified finite clock/width density spaces.'}
(root/'clock-independent-verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
