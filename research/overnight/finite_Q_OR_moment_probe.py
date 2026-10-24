"""Whole-word first-moment flux search for finite Q orbits; not a Lean proof."""
import argparse
from collections import deque
from fractions import Fraction
import json
from pathlib import Path
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from finite_Q_OR_rank_probe import Model,q
from stripe_prefix_dfa_potential import add


def moment_features(a,model):
    result={};state=2
    for k in range(a.bit_length()+model.r+3):
        code=(a>>k)&(model.patterns-1)
        if code or not state%2:add(result,(k%2*4+state)*model.patterns+code,k)
        state=model.advance(state,(a>>k)&1)
    return result


def controls(model):
    rng=random.Random(2026102408);count=0
    for _ in range(10000):
        width=rng.randrange(5,100);a=rng.getrandbits(width);history=[a]
        for _ in range(model.stride):history.append(q(history[-1]))
        if any(not x&3 for x in history):continue
        b=history[-1];u=(a&((1<<(model.size-1))-1),2,2,0,True);accum={}
        for k in range(width+model.size+4):
            bit=(a>>(k+model.size-1))&1;edge,=[e for e in model.edges[u] if e[4]==bit]
            for j,v in model.gain(edge).items():add(accum,j,k*v)
            u=edge[1]
        expected=moment_features(b,model)
        for j,v in moment_features(a,model).items():add(expected,j,-v)
        expected={j:v for j,v in expected.items() if v};assert accum==expected
        count+=1
        if count==128:break
    assert count==128
    return {'independent_first_moment_accounts':count,'all_passed':True}


def solve(model,seconds):
    depth={u:0 for u in model.sources};queue=deque(model.sources)
    while queue:
        u=queue.popleft()
        for e in model.edges[u]:
            v=e[1]
            if v in model.vertices and v not in depth:depth[v]=depth[u]+1;queue.append(v)
    assert len(depth)==len(model.vertices)
    D=model.dim;V=len(model.vertices)
    pot={u:2*D+i for i,u in enumerate(sorted(model.vertices))}
    rows=[];rhs=[]
    for u in model.sources:rows.append({pot[u]:-1});rhs.append(0)
    for u in model.vertices:
        for edge in model.edges[u]:
            v=edge[1]
            if v not in model.vertices:continue
            gain=model.gain(edge);c0=dict(gain);c1={D+j:val for j,val in gain.items()}
            add(c0,pot[u],1);add(c0,pot[v],-1);add(c0,pot[v]+V,-1)
            add(c1,pot[u]+V,1);add(c1,pot[v]+V,-1)
            if u[4]:rows.append(c0);rhs.append(-edge[5])
            else:
                for j,val in c1.items():add(c0,j,depth[u]*val)
                rows.append(c0);rhs.append(-edge[5]);rows.append(c1);rhs.append(0)
    for u in model.ends:
        rows.append({pot[u]:1,pot[u]+V:depth[u]});rhs.append(0)
        rows.append({pot[u]+V:1});rhs.append(0)
    data,cols,ptr=[],[],[0]
    for row in rows:
        for j,v in row.items():cols.append(j);data.append(v)
        ptr.append(len(data))
    dim=2*D+2*V;matrix=csr_matrix((data,cols,ptr),shape=(len(rows),dim))
    bounds=[(None,None)]*dim
    for p in (0,1):
        for state in range(8):
            if state%2:bounds[p*D+state*model.patterns]=(0,0)
    for j in range(8*model.patterns,D):bounds[D+j]=(0,0)
    fit=linprog(np.zeros(dim),A_ub=matrix,b_ub=rhs,bounds=bounds,method='highs-ds',
                options={'time_limit':seconds})
    report={'untrusted_synthesis_only':True,'Lean_verified':False,'full_problem_claim':False,
            'finite_OR_classification_proved':False,'moment_degree':1,'r':model.r,'stride':model.stride,
            'vertices':V,'variables':dim,'inequalities':len(rhs),'status':int(fit.status),
            'message':fit.message,'positivity_premise_used':False,'exact_LP_refutation':False}
    if fit.success:
        values=[Fraction(float(v)).limit_denominator(100000) for v in fit.x]
        exact=all(sum(v*values[j] for j,v in row.items())<=b for row,b in zip(rows,rhs))
        exact &= all(values[j]==lo for j,(lo,hi) in enumerate(bounds) if lo is not None and lo==hi)
        report.update(candidate=[str(v) for v in values],exact_rational_inequalities_passed=exact,
                      kernel_certificate_verified=False)
    return report


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--radius',type=int,default=2)
    ap.add_argument('--stride',type=int,choices=[1,2],default=1);ap.add_argument('--seconds',type=float,default=30)
    args=ap.parse_args();began=time.monotonic();model=Model(args.radius,args.stride)
    result=solve(model,args.seconds);result.update(controls=controls(model),seconds=round(time.monotonic()-began,3))
    Path(__file__).with_name('finite-Q-OR-moment-r'+str(args.radius)+'-s'+str(args.stride)+'.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in result.items() if k!='candidate'}))
