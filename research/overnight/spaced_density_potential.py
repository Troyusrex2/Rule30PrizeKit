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
from scipy.sparse import csr_matrix, vstack

from reachable_variation_potential import advance, features


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',type=int,default=3)
    ap.add_argument('--depth',type=int,default=49)
    ap.add_argument('--samples',type=int,default=128)
    ap.add_argument('--holdout-depth',type=int,default=1025)
    ap.add_argument('--renewal35',action='store_true',help='Require exact zero-bit spacings three or five')
    ap.add_argument('--method',choices=['highs','highs-ds','highs-ipm'],default='highs')
    ap.add_argument('--coefficient',type=float,help='Fix the output charge and minimize potential size')
    ap.add_argument('--bulk-controller',action='store_true',
                    help='Let all potential weights depend on the renewal controller state')
    ap.add_argument('--positional',action='store_true',
                    help='Use distance-weighted patterns and charge black output by its depth')
    ap.add_argument('--clock',type=int,default=2,help='Temporal phase period of the potential')
    ap.add_argument('--spatial-period',type=int,default=1,help='Separate pattern counts by spatial phase')
    ap.add_argument('--cut-rounds',type=int,default=0,help='Refit after adding independently reached counterexamples')
    ap.add_argument('--zero-suffix',type=int,default=0,
                    help='Only require descent when all three diagonals have this white suffix')
    args=ap.parse_args();started=time.monotonic()
    ages=5 if args.renewal35 else 3
    if args.clock%2 or args.clock<2 or args.spatial_period<1:raise ValueError('Use a positive even clock and positive spatial period')
    patterns=1 << (2*args.radius-1)
    phase_span=3*patterns*args.spatial_period
    plain_span=args.clock*phase_span
    span=plain_span*(3 if args.positional else 1)
    headbase=span*(ages if args.bulk_controller else 1)
    dim=headbase+2*ages+1
    def allowed(age,k):
        if k%2:return [1]
        if args.renewal35:
            return [0] if age==4 else [0,1] if age==2 else [1]
        return [0,1] if age==2 else [1]
    def vector(a,b,k,age):
        if args.clock==2 and args.spatial_period==1:
            out=features(a,b,k,args.radius,args.positional)
        else:
            out={};sm=(1 << args.radius)-1;lo=(1 << (args.radius-1))-1
            def add(group,code,i):
                j=(k%args.clock)*phase_span+(i%args.spatial_period)*3*patterns+group*patterns+code
                out[j]=out.get(j,0)+1
                if args.positional:
                    out[plain_span+j]=out.get(plain_span+j,0)+i
                    out[2*plain_span+j]=out.get(2*plain_span+j,0)+k-1-i
            for i in range(max(0,k-args.radius+1)):
                add(0,((a>>i)&sm)|(((b>>i)&lo)<<args.radius),i)
            if k>=args.radius:
                add(1,(a&sm)|((b&lo)<<args.radius),0)
                i=k-args.radius
                add(2,((a>>i)&sm)|(((b>>i)&lo)<<args.radius),i)
        if args.bulk_controller:out={j+age*span:v for j,v in out.items()}
        out[headbase+(k%2)*ages+age]=1
        return out
    def step(a,b,k,age,head):
        c=advance(a,b,k,head)
        nxtage=(0 if head==0 else min(ages-1,age+1)) if k%2==0 else age
        old=vector(a,b,k,age);new=vector(c,a,k+1,nxtage)
        for j,v in old.items():new[j]=new.get(j,0)-v
        cost=(c>>k)&1
        if args.positional:cost*=k+1
        new[dim-1]=-cost
        return c,nxtage,new,int(k%2==0)
    def selected(a,b,c,k):
        size=args.zero_suffix
        if not size:return True
        if k-1<size:return False
        return (a>>(k-size))==0 and (b>>(k-1-size))==0 and (c>>(k+1-size))==0
    data=[];indices=[];indptr=[0];rhs=[];states=[(0,0,2)]
    for k in range(args.depth):
        nxt=[]
        for a,b,age in states:
            heads=allowed(age,k)
            for head in heads:
                c,na,row,reward=step(a,b,k,age,head);nxt.append((c,a,na))
                if k<args.radius or not selected(a,b,c,k):continue
                for j,v in row.items():
                    if v:data.append(v);indices.append(j)
                indptr.append(len(data));rhs.append(-reward)
        states=nxt
        if k%8==0:print(json.dumps({'depth':k+1,'states':len(states),'constraints':len(rhs)}),flush=True)
    if not rhs:raise RuntimeError('No selected descent cases; no candidate is meaningful')
    mat=csr_matrix((data,indices,indptr),shape=(len(rhs),dim),dtype=float)
    target=np.zeros(dim);target[-1]=1
    bounds=[(0,None)]*dim
    if args.coefficient is not None:
        bounds[-1]=(args.coefficient,args.coefficient);target[:]=1;target[-1]=0
    report={'finite_synthesis_only':True,'density_proved':False,'CQ01Empty_proved':False,
            'radius':args.radius,'training_depth':args.depth,'constraints':len(rhs),
            'exact_three_or_five':args.renewal35,
            'method':args.method,'fixed_coefficient':args.coefficient,
            'bulk_weights_depend_on_controller':args.bulk_controller,
            'output_charge_by_depth':args.positional,
            'temporal_clock':args.clock,'spatial_period':args.spatial_period,'fit_rounds':[]}
    report['white_suffix_required']=args.zero_suffix
    for round_index in range(args.cut_rounds+1):
        report['constraints']=int(mat.shape[0])
        fit=linprog(target,A_ub=mat,b_ub=rhs,bounds=bounds,method=args.method,
                    options={'time_limit':120})
        report.update(status=int(fit.status),message=fit.message)
        if not fit.success:
            if 'weights' in report:report['last_rejected_weights']=report.pop('weights')
            report['current_candidate_available']=False
            break
        report['current_candidate_available']=True
        report.update(coefficient=float(fit.x[-1]),weights=fit.x.tolist(),
            training_max_residual=float(np.max(mat@fit.x-np.array(rhs))))
        rng=random.Random(20261024);witness=None;checked=0;cut=None;cut_rhs=None
        for sample in range(args.samples):
            a=b=0;age=2;free=[];initial=[]
            for k in range(args.holdout_depth):
                head=rng.choice(allowed(age,k))
                if k%2==0:free.append(head)
                c,na,row,reward=step(a,b,k,age,head)
                initial.append((c>>k)&1)
                consider=selected(a,b,c,k)
                a,b,age=c,a,na
                if k<args.radius or not consider:continue
                residual=sum(v*fit.x[j] for j,v in row.items())+reward;checked+=1
                if residual>1e-6:
                    witness={'sample':sample,'depth':k+1,'residual':float(residual),
                             'diagonals':[a,b],'age':age,
                             'free_prefix':''.join(map(str,free)),
                             'initial_prefix':''.join(map(str,initial))}
                    # Independent ordinary zero-boundary forward evolution.
                    packed=sum(x<<i for i,x in enumerate(initial))
                    for t in range(k+1):
                        assert packed&1==(1 if t%2 else free[t//2])
                        packed=(packed>>1)^(packed|(packed<<1))
                    witness['ordinary_forward_control']=True
                    cut=row;cut_rhs=-reward;break
            if witness:break
        report.update(holdout_steps=checked,holdout_counterexample=witness,
                      candidate_rejected=witness is not None,universal_invariant_checked=False)
        record={'round':round_index,'status':int(fit.status),'coefficient':float(fit.x[-1]),
                'holdout_steps':checked,'counterexample':witness}
        report['fit_rounds'].append(record)
        print(json.dumps({'fit_round':round_index,'counterexample_depth':None if witness is None else witness['depth'],
                          'holdout_steps':checked}),flush=True)
        if witness is None or round_index==args.cut_rounds:break
        js=list(cut);vs=[cut[j] for j in js]
        extra=csr_matrix((vs,js,[0,len(js)]),shape=(1,dim),dtype=float)
        mat=vstack([mat,extra],format='csr');rhs.append(cut_rhs)
    report['seconds']=round(time.monotonic()-started,3)
    suffix='-renewal35' if args.renewal35 else ''
    if args.coefficient is not None:suffix+=f'-c{args.coefficient:g}'
    if args.method!='highs':suffix+='-'+args.method
    if args.bulk_controller:suffix+='-bulk-controller'
    if args.positional:suffix+='-positional'
    if args.clock!=2:suffix+=f'-clock{args.clock}'
    if args.spatial_period!=1:suffix+=f'-space{args.spatial_period}'
    if args.cut_rounds:suffix+=f'-cuts{args.cut_rounds}'
    if args.zero_suffix:suffix+=f'-zero{args.zero_suffix}'
    (Path(__file__).parent/f'spaced-density-potential-r{args.radius}{suffix}-d{args.depth}.json').write_text(
        json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in
        ['weights','last_rejected_weights','fit_rounds','holdout_counterexample']} |
        {'counterexample_depths':[x['counterexample']['depth'] for x in report['fit_rounds'] if x['counterexample']]}))


if __name__=='__main__':main()
