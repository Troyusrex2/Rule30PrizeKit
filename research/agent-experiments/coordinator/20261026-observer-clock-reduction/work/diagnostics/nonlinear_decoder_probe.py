"""Exhaustive truth-table tests for low-degree temporal Boolean decoders.
The generated algebra layer spans all head-time monomials up to that degree.
A successful finite layer is NOT an all-width observer certificate.
"""
from pathlib import Path
import json,time,numpy as np
r=Path(__file__).resolve().parent;START=time.monotonic();reports=[]
def encode(z,m):
    bits=[(z>>i)&1 for i in range(m)];i=next((i for i,x in enumerate(bits) if x),m)
    return [0]+bits if i>=m-2 else bits[:i+2]+[bits[i+1]]+bits[i+2:]
def table(n):
    m=n-1;M=1<<m;P=1<<((2*n-1)//3)
    rows=np.array([sum(x<<i for i,x in enumerate(encode(z,m))) for z in range(M)],dtype=np.uint32)
    assert len(set(map(int,rows)))==M
    initial=rows.copy();observations=[]
    for t in range(P):
        observations.append(int.from_bytes(np.packbits((rows>>(n-1))&1,bitorder='little').tobytes(),'little'))
        rows=(rows^((rows<<1)|(rows<<2)))&((1<<n)-1)
    assert np.array_equal(rows,initial)
    targets=[int.from_bytes(np.packbits((np.arange(M,dtype=np.uint32)>>j)&1,bitorder='little').tobytes(),'little') for j in range(m)]
    return M,P,list(dict.fromkeys(observations)),targets
def residue(v,basis):
    while v:
        p=v.bit_length()-1
        if p not in basis:return v
        v^=basis[p]
    return 0
for n in range(3,14):
    begin=time.monotonic();M,P,obs,targets=table(n)
    basis={M-1:(1<<M)-1};layers=[];complete=True
    for degree in range(1,5):
        prev=list(basis.values());products=0
        for b in prev:
            for h in obs:
                v=residue(b&h,basis)
                if v:basis[v.bit_length()-1]=v
                products+=1
            if time.monotonic()-START>140:complete=False;break
        recovered=[j for j,v in enumerate(targets) if residue(v,basis)==0]
        layer={'degree':degree,'rank':len(basis),'recovered_coordinates':recovered,'products_checked':products}
        layers.append(layer)
        if len(recovered)==len(targets) or not complete:break
    out={'width':n,'rows':M,'working_period':P,'unique_observation_functions':len(obs),
         'layers':layers,'complete_code_recovered':len(recovered)==len(targets),'complete_layers':complete,
         'seconds':round(time.monotonic()-begin,3)}
    reports.append(out);print(json.dumps(out),flush=True)
    (r/'nonlinear-decoder-probe.json').write_text(json.dumps({'reports':reports,'Lean_verified':False,
        'canonical_observer_proved':False,'full_problem_solved':False},indent=2)+'\n',encoding='utf-8')
    if not complete:break
