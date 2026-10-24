"""Search a local nonnegative amortized potential for the reconstruction.

Reachable adjacent anti-diagonals A,B satisfy B_i <= A_i xor A_(i+1).
That invariant is preserved by the prefix-xor/OR update. The LP checks all
compatible ribbons up to a chosen width; floating-point feasibility is only a
candidate and never a mathematical proof of an unbounded estimate.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog


def features(a,b,k,phase):
    v=np.zeros(33,dtype=np.int16)
    for i in range(k-1):
        code=4*((a>>i)&1)+2*((a>>(i+1))&1)+((b>>i)&1)
        v[phase*8+code]+=1
    v[16+phase*4+2*(a&1)+(b&1)]+=1
    v[24+phase*4+2*((a>>(k-1))&1)+((b>>(k-2))&1)]+=1
    return v


def next_diag(a,b,k,head):
    out=head;carry=head
    for i in range(k):
        carry ^= ((a>>i)&1) | (((b>>(i-1))&1) if i else 0)
        out |= carry<<(i+1)
    return out


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--width',type=int,default=10)
    ap.add_argument('--two-sided-ribbon',action='store_true')
    ap.add_argument('--signed-potential',action='store_true')
    args=ap.parse_args();began=time.monotonic()
    rows=[];rhs=[]
    for k in range(2,args.width+1):
        phase=k%2
        for a in range(1<<k):
            if phase==1 and not(a&1):continue
            transitions=(a^(a>>1))&((1<<(k-1))-1)
            b=transitions
            while True:
                compatible = not args.two_sided_ribbon or not (transitions & ~(b | (b<<1)))
                if compatible and (phase or b&1):
                    old=features(a,b,k,phase)
                    for head in ([1] if phase==0 else [0,1]):
                        c=next_diag(a,b,k,head)
                        assert ((c^(c>>1))&a)==a
                        if args.two_sided_ribbon:
                            ct=(c^(c>>1))&((1<<k)-1)
                            assert not (ct & ~(a | (a<<1)))
                        new=features(c,a,k+1,1-phase)
                        row=new-old
                        row[32]=-((c>>k)&1)
                        reward=int(phase==1 and (b&1)!=head)
                        rows.append(row);rhs.append(-reward)
                        if args.signed_potential:
                            rows.extend([-old,-new]);rhs.extend([0,0])
                if b==0:break
                b=(b-1)&transitions
        print(json.dumps({'width':k,'constraints':len(rows)}),flush=True)
    objective=np.zeros(33);objective[32]=1
    bounds=([(None,None)]*32+[(0,None)] if args.signed_potential else [(0,None)]*33)
    for phase in [0,1]:
        for code in [1,7]:bounds[phase*8+code]=(0,0)
    matrix=np.array(rows,dtype=float);bound=np.array(rhs,dtype=float)
    result=linprog(objective,A_ub=matrix,b_ub=bound,bounds=bounds,method='highs')
    report={'finite_lp_only':True,'unbounded_estimate_proved':False,
            'local_invariant':'B_i implies A_i xor A_(i+1)',
            'upper_ribbon_bound':args.two_sided_ribbon,
            'signed_potential':args.signed_potential,
            'max_width':args.width,'constraints':len(rows),'status':int(result.status),
            'message':result.message,'seconds':round(time.monotonic()-began,3)}
    if result.success:
        rational=[str(Fraction(float(x)).limit_denominator(10000)) for x in result.x]
        report.update(candidate_coefficient=float(result.x[32]),candidate_weights=rational,
                      maximum_float_residual=float(np.max(matrix@result.x-bound)))
    name=('variation-potential-signed-lp.json' if args.signed_potential else
          'variation-potential-ribbon-lp.json' if args.two_sided_ribbon else 'variation-potential-lp.json')
    (Path(__file__).parent/name).write_text(
        json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':main()
