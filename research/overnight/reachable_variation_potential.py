"""Falsifiable potential synthesis; finite feasibility is never a proof.

Train only on exactly reachable reconstruction diagonals. Test any numerical
candidate on independently sampled much longer histories. The stronger task,
proving an invariant and its universal preservation, remains separate.
"""
import argparse
import json
from pathlib import Path
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

HERE = Path(__file__).resolve().parent


def px(v, n):
    shift = 1
    while shift < n:
        v ^= v << shift
        shift *= 2
    return v & ((1 << n) - 1)


def advance(a, b, k, head):
    return ((px(a | (b << 1), k) ^ (((1 << k)-1) if head else 0)) << 1) | head


def features(a, b, k, radius, positional=False):
    patterns = 1 << (2*radius-1)
    offset = (k % 2)*3*patterns
    small = (1 << radius)-1
    lower = (1 << (radius-1))-1
    out = {}; span=6*patterns
    def add(code,position):
        out[code]=out.get(code,0)+1
        if positional:
            out[span+code]=out.get(span+code,0)+position
            out[2*span+code]=out.get(2*span+code,0)+k-1-position
    for i in range(max(0, k-radius+1)):
        code = ((a >> i) & small) | (((b >> i) & lower) << radius)
        add(offset+code,i)
    if k >= radius:
        head = (a & small) | ((b & lower) << radius)
        i = k-radius
        tail = ((a >> i) & small) | (((b >> i) & lower) << radius)
        add(offset+patterns+head,0)
        add(offset+2*patterns+tail,i)
    return out


def constraint(a, b, k, head, radius, growth=1, positional=False):
    c = advance(a,b,k,head)
    old = features(a,b,k,radius,positional)
    new = features(c,a,k+1,radius,positional)
    cost = (c >> k) & 1
    for j,v in old.items(): new[j] = new.get(j,0)-(growth if cost else 1)*v
    reward = int(k%2 == 1 and (b&1) != head)
    return c,new,cost,reward


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',type=int,default=3)
    ap.add_argument('--depth',type=int,default=27)
    ap.add_argument('--holdout-depth',type=int,default=1025)
    ap.add_argument('--samples',type=int,default=256)
    ap.add_argument('--growth',type=int,default=1,
                    help='Allow multiplicative growth of potential at a black output')
    ap.add_argument('--positional',action='store_true',
                    help='Track distance-weighted patterns; charge output at its depth')
    args = ap.parse_args()
    started = time.monotonic(); dim = 6*(1 << (2*args.radius-1))*(3 if args.positional else 1)+1
    entries=[]; indices=[]; indptr=[0]; rhs=[]
    states=[(0,0)]
    for k in range(args.depth):
        nxt=[]
        for a,b in states:
            for h in ([1] if k%2==0 else [0,1]):
                c,row,cost,reward=constraint(a,b,k,h,args.radius,args.growth,args.positional)
                if args.positional: cost *= k+1
                nxt.append((c,a))
                if k < args.radius: continue
                row[dim-1] = -cost
                for j,v in row.items():
                    if v: indices.append(j);entries.append(v)
                indptr.append(len(entries));rhs.append(-reward)
        states=nxt
        print(json.dumps({'depth':k+1,'states':len(states),'constraints':len(rhs)}),flush=True)
    mat=csr_matrix((entries,indices,indptr),shape=(len(rhs),dim),dtype=float)
    target=np.zeros(dim);target[-1]=1
    fit=linprog(target,A_ub=mat,b_ub=rhs,bounds=[(0,None)]*dim,method='highs')
    report={'finite_synthesis_only':True,'unbounded_estimate_proved':False,
            'radius':args.radius,'training_depth':args.depth,'constraints':len(rhs),
            'growth_at_black_output':args.growth,
            'distance_weighted_potential':args.positional,
            'status':int(fit.status),'message':fit.message}
    if fit.success:
        report['coefficient']=float(fit.x[-1]); report['weights']=fit.x.tolist()
        report['training_max_residual']=float(np.max(mat@fit.x-np.array(rhs)))
        rng=random.Random(20261024); witness=None;tested=0
        for sample in range(args.samples):
            a=b=0
            for k in range(args.holdout_depth):
                head=1 if k%2==0 else rng.randrange(2)
                c,row,cost,reward=constraint(a,b,k,head,args.radius,args.growth,args.positional)
                if args.positional: cost *= k+1
                a,b=c,a
                if k < args.radius:continue
                residual=sum(v*fit.x[j] for j,v in row.items())+reward-cost*fit.x[-1]
                tested+=1
                if residual>1e-6:
                    witness={'sample':sample,'depth':k+1,'residual':float(residual),
                             'diagonals':[a,b]};break
            if witness:break
        report.update(holdout_steps=tested,holdout_counterexample=witness,
                      universal_invariant_checked=False,
                      candidate_rejected=witness is not None)
    report['seconds']=round(time.monotonic()-started,3)
    suffix=f'-growth{args.growth}' if args.growth!=1 else ''
    if args.positional:suffix+='-positional'
    path=HERE/f'reachable-potential-r{args.radius}{suffix}.json'
    path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k!='weights'}))


if __name__=='__main__':main()
