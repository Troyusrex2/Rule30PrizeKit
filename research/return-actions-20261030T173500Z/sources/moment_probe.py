"""One uniform proof attempt: local charge weighted by spatial position.
An affine graph potential telescopes for every spatial word length. If a
rational certificate exists, the resulting quadratic bound suffices for
rigidity; no need to prove the guessed linear rate. r2,3,4 only;20s each.
"""
from pathlib import Path
from fractions import Fraction
from math import lcm
import json,time,numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
R=Path(__file__).resolve().parent;start=time.monotonic();results=[]
def f(a,b,c):return 2*((c>>1)^((b>>1)|(a>>1)))+((c&1)^((b&1)|(a&1)))
for r in [2,3,4]:
    dim=4**r;nv=4**(r+1)
    diag=lambda w,n:all(((w>>(2*i))&3) in (0,3) for i in range(n))
    nodes=[v for v in range(nv) if diag(v,r+1)]+list(range(nv,2*nv))
    index={v:i for i,v in enumerate(nodes)};nc=len(nodes);variables=dim+2*nc
    Aidx=lambda v:dim+index[v]
    Bidx=lambda v:dim+nc+index[v]
    rows=[];cols=[];values=[];rhs=[]
    def add(items,b):
        row=len(rhs)
        for col,value in items:rows.append(row);cols.append(col);values.append(value)
        rhs.append(b)
    for state in nodes:
        v=state%nv;seen=state//nv;digits=[(v>>s)&3 for s in range(2*r,-1,-2)]
        for e in range(4):
            w=digits+[e];out=0
            for j in range(r):out=4*out+f(*w[j:j+3])
            inp=((v&(dim//4-1))<<2)|e
            target=(((v&(nv//4-1))<<2)|e)+nv*(seen or e in (1,2))
            # (i+1)*dq >= (i+1)*a_t+b_t-i*a_s-b_s for every i>=0.
            add([(out,-1),(inp,1),(Aidx(target),1),(Aidx(state),-1)],0)
            add([(out,-1),(inp,1),(Aidx(target),1),(Bidx(target),1),(Bidx(state),-1)],0)
    for v in range(nv):
        if diag(v,r+1):add([(Aidx(nv+v),-1)],0);add([(Bidx(nv+v),-1)],-1)
    mat=coo_matrix((values,(rows,cols)),shape=(len(rhs),variables)).tocsr()
    bounds=[(0,0) if diag(w,r) else (None,None) for w in range(dim)]+[(None,None)]*(2*nc)
    bounds[Bidx(3)]=(0,0)
    lp=linprog(np.zeros(variables),A_ub=mat,b_ub=np.array(rhs),bounds=bounds,
               method='highs',options=dict(time_limit=20.))
    result=dict(radius=r,variables=variables,inequalities=len(rhs),status=int(lp.status),message=lp.message,
                exact_certificate=False)
    if lp.success:
        coeff=[Fraction(float(a)).limit_denominator(1000000) for a in lp.x]
        den=lcm(*(v.denominator for v in coeff));v=[int(a*den) for a in coeff]
        ok=all(sum(int(mat.data[p])*v[int(mat.indices[p])] for p in range(mat.indptr[k],mat.indptr[k+1]))<=b*den
               for k,b in enumerate(rhs))
        result['exact_certificate']=ok
        if ok:(R/('MOMENT_CERT_R'+str(r)+'.json')).write_text(json.dumps(dict(radius=r,scale=den,q=v[:dim],
             affine=[dict(node=node,a=v[Aidx(node)],b=v[Bidx(node)]) for node in nodes]),indent=2)+'\n')
    results.append(result)
(R/'MOMENT_PROBE.json').write_text(json.dumps(dict(results=results,seconds=time.monotonic()-start,
    scope='Tests a sufficient affine graph-coboundary proof for a spatially weighted local charge. Infeasible floating solver status is not a theorem excluding all moments or potentials.'),indent=2)+'\n')
print(json.dumps(dict(results=results,seconds=round(time.monotonic()-start,3))))
