"""Search a falsifiable density potential for a spaced white-first gate.

This is numerical candidate synthesis, not proof of any density bound or Q01.
The input controller enforces at least two ones between zero free bits. The
actual empty-right gate now has an independently certified stronger restriction.
"""
import argparse
import json
from pathlib import Path
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from reachable_variation_potential import advance, features


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',type=int,default=3)
    ap.add_argument('--depth',type=int,default=49)
    ap.add_argument('--samples',type=int,default=128)
    ap.add_argument('--holdout-depth',type=int,default=1025)
    ap.add_argument('--renewal35',action='store_true',help='Require exact zero-bit spacings three or five')
    args=ap.parse_args();started=time.monotonic()
    ages=5 if args.renewal35 else 3
    span=6*(1 << (2*args.radius-1));dim=span+2*ages+1
    def allowed(age,k):
        if k%2:return [1]
        if args.renewal35:
            return [0] if age==4 else [0,1] if age==2 else [1]
        return [0,1] if age==2 else [1]
    def vector(a,b,k,age):
        out=features(a,b,k,args.radius)
        out[span+(k%2)*ages+age]=1
        return out
    def step(a,b,k,age,head):
        c=advance(a,b,k,head)
        nxtage=(0 if head==0 else min(ages-1,age+1)) if k%2==0 else age
        old=vector(a,b,k,age);new=vector(c,a,k+1,nxtage)
        for j,v in old.items():new[j]=new.get(j,0)-v
        cost=(c>>k)&1;new[dim-1]=-cost
        return c,nxtage,new,int(k%2==0)
    data=[];indices=[];indptr=[0];rhs=[];states=[(0,0,2)]
    for k in range(args.depth):
        nxt=[]
        for a,b,age in states:
            heads=allowed(age,k)
            for head in heads:
                c,na,row,reward=step(a,b,k,age,head);nxt.append((c,a,na))
                if k<args.radius:continue
                for j,v in row.items():
                    if v:data.append(v);indices.append(j)
                indptr.append(len(data));rhs.append(-reward)
        states=nxt
        if k%8==0:print(json.dumps({'depth':k+1,'states':len(states),'constraints':len(rhs)}),flush=True)
    mat=csr_matrix((data,indices,indptr),shape=(len(rhs),dim),dtype=float)
    target=np.zeros(dim);target[-1]=1
    fit=linprog(target,A_ub=mat,b_ub=rhs,bounds=[(0,None)]*dim,method='highs')
    report={'finite_synthesis_only':True,'density_proved':False,'CQ01Empty_proved':False,
            'radius':args.radius,'training_depth':args.depth,'constraints':len(rhs),
            'exact_three_or_five':args.renewal35,
            'status':int(fit.status),'message':fit.message}
    if fit.success:
        report.update(coefficient=float(fit.x[-1]),weights=fit.x.tolist(),
            training_max_residual=float(np.max(mat@fit.x-np.array(rhs))))
        rng=random.Random(20261024);witness=None;checked=0
        for sample in range(args.samples):
            a=b=0;age=2
            for k in range(args.holdout_depth):
                head=rng.choice(allowed(age,k))
                c,na,row,reward=step(a,b,k,age,head)
                a,b,age=c,a,na
                if k<args.radius:continue
                residual=sum(v*fit.x[j] for j,v in row.items())+reward;checked+=1
                if residual>1e-6:
                    witness={'sample':sample,'depth':k+1,'residual':float(residual),
                             'diagonals':[a,b],'age':age};break
            if witness:break
        report.update(holdout_steps=checked,holdout_counterexample=witness,
                      candidate_rejected=witness is not None,universal_invariant_checked=False)
    report['seconds']=round(time.monotonic()-started,3)
    suffix='-renewal35' if args.renewal35 else ''
    (Path(__file__).parent/f'spaced-density-potential-r{args.radius}{suffix}-d{args.depth}.json').write_text(
        json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k!='weights'}))


if __name__=='__main__':main()
