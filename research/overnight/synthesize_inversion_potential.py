"""Falsifiable nonlocal potential synthesis using ordered pairs of ribbon letters.

Unlike the local graph model, inversion counts retain some ordering information.
Finite fits, solver infeasibility and holdout failures remain experimental.
"""
import argparse
import json
from pathlib import Path
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, vstack

from reachable_variation_potential import advance
from synthesize_transducer_potential import Model

HERE=Path(__file__).resolve().parent


def base_features(a,b,k,adjacent=True):
    counts=[0]*3;inversions=[0]*9;neighbors=[0]*16;last=None
    for i in range(k):
        letter=((a>>i)&1)+2*(((b>>(i-1))&1) if i else 0)
        if adjacent and last is not None:neighbors[4*last+letter]+=1
        if letter:
            for old in range(3):inversions[3*old+letter-1]+=counts[old]
            counts[letter-1]+=1
        last=letter
    return counts+inversions+(neighbors if adjacent else [])


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cycles',type=int,default=49)
    ap.add_argument('--suffix',type=int,default=3)
    ap.add_argument('--reward',choices=['cycle','short-gap','long-gap'],default='short-gap')
    ap.add_argument('--cuts',type=int,default=5)
    ap.add_argument('--holdout-cycles',type=int,default=1025)
    ap.add_argument('--samples',type=int,default=128)
    args=ap.parse_args();started=time.monotonic()
    width=28;dim=5*(width+1)
    def feature(a,b,k,age):
        out=np.zeros(dim,dtype=np.int64)
        out[age*(width+1):age*(width+1)+width]=base_features(a,b,k)
        out[age*(width+1)+width]=1
        return out
    def selected(a,b,c,d,k):
        s=args.suffix
        return k-1>=s and a>>(k-s)==0 and b>>(k-1-s)==0 and c>>(k+1-s)==0 and d>>(k+2-s)==0
    def reward(age,head):
        return int(args.reward=='cycle' or args.reward=='short-gap' and age==2 and head==0 or
                   args.reward=='long-gap' and age==4 and head==0)
    def inequality(a,b,c,d,k,age,h):
        na=Model.nextage(0,age,h)
        return feature(d,c,k+2,na)-feature(a,b,k,age),-reward(age,h)
    states=[(0,0,2)];rows=[];rhs=[]
    for cycle in range(args.cycles):
        k=2*cycle;nxt=[]
        for a,b,age in states:
            for h in Model.allowed(0,age):
                c=advance(a,b,k,h);d=advance(c,a,k+1,1);na=Model.nextage(0,age,h)
                nxt.append((d,c,na))
                if selected(a,b,c,d,k):
                    row,right=inequality(a,b,c,d,k,age,h);rows.append(row);rhs.append(right)
        states=nxt
        if cycle%8==0:print(json.dumps({'cycles':cycle+1,'states':len(states),'selected':len(rhs)}),flush=True)
    matrix=csr_matrix(np.array(rows,dtype=float))
    if not any(right<0 for right in rhs):raise RuntimeError('No positive-reward training cases')
    report={'finite_synthesis_only':True,'nonlocal_ordered_pair_features':True,
            'CQ01Empty_proved':False,'potential_proved':False,'training_cycles':args.cycles,
            'suffix':args.suffix,'reward':args.reward,'variables':dim,'rounds':[]}
    for iteration in range(args.cuts+1):
        fit=linprog(np.ones(dim),A_ub=matrix,b_ub=rhs,bounds=(0,None),method='highs-ds',options={'time_limit':120})
        report.update(status=int(fit.status),message=fit.message,inequalities=int(matrix.shape[0]))
        if not fit.success:break
        rng=random.Random(20261024);witness=None;cut=None;cut_rhs=None;checked=0
        for sample in range(args.samples):
            a=b=0;age=2;heads=[];initial=[]
            for cycle in range(args.holdout_cycles):
                k=2*cycle;h=rng.choice(Model.allowed(0,age));heads.extend([h,1])
                c=advance(a,b,k,h);d=advance(c,a,k+1,1)
                initial.extend([(c>>k)&1,(d>>(k+1))&1])
                if selected(a,b,c,d,k):
                    row,right=inequality(a,b,c,d,k,age,h)
                    residual=float(row@fit.x-right);checked+=1
                    if residual>1e-6:
                        packed=sum(x<<i for i,x in enumerate(initial))
                        for expected in heads:
                            assert packed&1==expected
                            packed=(packed>>1)^(packed|(packed<<1))
                        witness={'sample':sample,'old_width':k,'residual':residual,
                                 'old_pair':[a,b],'age':age,'head':h,'ordinary_forward_checked':True,
                                 'boundary_prefix':''.join(map(str,heads)),
                                 'initial_prefix':''.join(map(str,initial))}
                        cut=row;cut_rhs=right;break
                a,b,age=d,c,Model.nextage(0,age,h)
            if witness:break
        report['rounds'].append({'round':iteration,'tested_descent_cases':checked,'counterexample':witness})
        report.update(last_fitted_weights=fit.x.tolist(),universal_invariant_checked=False)
        print(json.dumps({'fit_round':iteration,'tested':checked,'counterexample_width':None if witness is None else witness['old_width']}),flush=True)
        if witness is None or iteration==args.cuts:break
        matrix=vstack([matrix,csr_matrix(cut.reshape(1,-1))],format='csr');rhs.append(cut_rhs)
    report['seconds']=round(time.monotonic()-started,3)
    target=HERE/f'inversion-potential-cycles{args.cycles}-zero{args.suffix}-{args.reward}-cuts{args.cuts}.json'
    target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['last_fitted_weights','rounds']}))


if __name__=='__main__':main()
