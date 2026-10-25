"""A nonnegative cone of squared affine global-count potentials.

Positive fitted weights remain provisional. Held-out and universal proof
obligations are separate from numerical feasibility.
"""
import argparse,itertools,json,random,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from core import HERE,save
from zero_tail_rank import transitions,random_free,controls
from even_code_charge import words
from empty_right_absorption import step as right_step

def count(word):return np.array([word.count(i) for i in range(4)]+[1],dtype=np.int64)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--paths',type=int,default=128)
    parser.add_argument('--coefficient-bound',type=int,default=1);parser.add_argument('--scaled',action='store_true')
    args=parser.parse_args()
    checked=controls();rng=random.Random(302455);start=time.monotonic()
    fs=[]
    for f in itertools.product(range(-args.coefficient_bound,args.coefficient_bound+1),repeat=5):
        if not any(f) or next(v for v in f if v)!=abs(next(v for v in f if v)):continue
        from math import gcd
        g=0
        for v in f:g=gcd(g,abs(v))
        if g==1:fs.append(f)
    F=np.array(fs,dtype=np.int64);m=len(F)
    train=[[w>>i&1 for i in range(12)] for w in words(12,True)]+[random_free(64,rng) for _ in range(args.paths)]
    held=[random_free(128,rng) for _ in range(64)]
    for name in ['charge-beam-factor3.json','charge-beam-factor8.json']:
        held += [r['free_prefix'] for r in json.loads((HERE/name).read_text())['records']]
    for R in [0,1,2,3,5,17,31,495,255]:
        x=R;free=[]
        for t in range(512):
            x=right_step(x,t)
            if t%2==0:free.append(1^(x&1))
        held.append(free)
    edges=[];seen=set()
    for free in train:
        prefix=0
        for e in transitions(free):
            d=e[-1];prefix|=free[d]<<d
            if e[-2]==0 and (d,prefix) not in seen:edges.append(e);seen.add((d,prefix))
    ii=[];jj=[];data=[];rhs=[]
    for i,e in enumerate(edges):
        before,r,after,rr,s,_,_=e;rhs.append(-(1-s))
        old=(F@count(before))**2;new=(F@count(after))**2
        for j in np.flatnonzero(old):ii.append(i);jj.append(r*m+int(j));data.append(-int(old[j]))
        for j in np.flatnonzero(new):ii.append(i);jj.append(rr*m+int(j));data.append(int(new[j]))
    A=coo_matrix((data,(ii,jj)),shape=(len(edges),5*m)).tocsr()
    scales=1/np.maximum(1,np.abs(A).max(axis=1).toarray().ravel()) if args.scaled else np.ones(len(edges))
    result=linprog(np.ones(5*m),A_ub=A.multiply(scales[:,None]).tocsr(),b_ub=np.array(rhs)*scales,bounds=(0,None),
                   method='highs-ds' if args.scaled else 'highs',options={'time_limit':60,
                       'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
    out={'coefficient_bound':args.coefficient_bound,'squared_forms':m,'variables':5*m,
         'training_edges':len(edges),'solver_status':int(result.status),'solver_message':result.message,
         'controls':checked,'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False,
         'row_scaling':args.scaled}
    if result.success:
        W=result.x.reshape(5,m);out['nonzero_weights']=int(np.count_nonzero(W>1e-10))
        out['training_max_residual']=float(np.max(A@result.x-np.array(rhs)))
        violations=[];total=0
        for free in held:
            for e in transitions(free):
                before,r,after,rr,s,even,d=e
                if even:continue
                total+=1
                res=float(W[rr]@((F@count(after))**2)-W[r]@((F@count(before))**2)+(1-s))
                if res>1e-6:violations.append({'length':d+1,'residual':res})
        out['heldout_edges']=total;out['heldout_violations']=len(violations);out['first_violations']=violations[:8]
        if not violations:
            out['provisional_weights']=[{'run':r,'form':fs[j],'weight':float(W[r,j])}
                for r in range(5) for j in range(m) if W[r,j]>1e-10]
    out['seconds']=round(time.monotonic()-start,3)
    save(f'zero-tail-squares-bound{args.coefficient_bound}'+('-scaled' if args.scaled else '')+'.json',out)
    print({k:v for k,v in out.items() if k not in ('provisional_weights','first_violations')},flush=True)

if __name__=='__main__':main()
