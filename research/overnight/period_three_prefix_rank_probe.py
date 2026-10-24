"""Finite falsification of a period-three left-half prefix score candidate.

No successful numerical fit is a proof. No numerical infeasibility is treated
as an exact impossibility certificate. The two references are period-three
ether left halves; their scalar dynamics and the three-cell constraint are
checked independently before any optimization.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix


ETHER = ((0,0,1),(0,0,1),(0,1,1),(1,1,0),(0,1,0),(0,1,0),
         (1,1,0),(1,0,1),(1,0,0),(1,0,0),(1,0,1),(0,1,1))
BASE = [[ETHER[(2-k)%12][0] for k in range(1,13)],
        [ETHER[(3-k)%12][2] for k in range(1,13)]]


def step(a, b):
    return (a>>1) ^ (a | (a<<1) | b)


def cycle(a):
    return step(step(step(a,0),1),0)


def good(a):
    return a&7 in (0,7)


def scalar_cycle(a, width):
    cells = [(a>>i)&1 for i in range(width)]+[0]*6
    for b in (0,1,0):
        cells = [cells[i+1] ^ (cells[i] | (b if i==0 else cells[i-1]))
                 for i in range(len(cells)-1)]
    return sum(c<<i for i,c in enumerate(cells))


class Model:
    def __init__(self, r, modulus, prefix):
        self.r,self.modulus,self.prefix = r,modulus,prefix
        self.patterns=1<<r
        self.states=2*modulus*(2 if prefix else 1)
        self.dim=self.states*self.patterns+2

    def features(self,a):
        mode=a&1
        matched=True
        result={self.dim-2:1,self.dim-1:mode}
        for i in range(a.bit_length()+12+self.r):
            bit=(a>>i)&1
            code=(a>>i)&(self.patterns-1)
            state=(mode*self.modulus+i%self.modulus)*(2 if self.prefix else 1)
            if self.prefix:
                state+=int(matched)
            if code or self.prefix and matched:
                j=state*self.patterns+code
                result[j]=result.get(j,0)+1
            if bit!=BASE[mode][i%12]:matched=False
        return result

    def bounds(self):
        result=[(None,None)]*self.dim
        for state in range(self.states):
            # Zero tails contribute no infinite background charge.
            if not self.prefix or state%2==0:result[state*self.patterns]=(0,0)
        return result


def controls():
    count=0
    for a in range(256):
        assert cycle(a)==scalar_cycle(a,8)
        t1=step(a,0);t2=step(t1,1)
        assert good(a)==((t1&1)==0 and (t2&1)==1)
        count+=1
    for base in BASE:
        a=sum(base[i%12]<<i for i in range(120))
        assert cycle(a)&((1<<100)-1)==a&((1<<100)-1)
    return {'packed_vs_scalar_examples':count,'first_three_uniform_constraint':True,
            'two_ether_reference_cycles':True}


def fit(width, age, model, charge, seconds):
    values,cols,ptr,rhs=[],[],[0],[]
    accepted=flips=0
    def append(row,bound):
        for j,v in row.items():
            if v:cols.append(j);values.append(float(v))
        ptr.append(len(values));rhs.append(bound)
    began=time.monotonic()
    for a in range(1<<width):
        x=a
        valid=True
        for _ in range(age):
            if not good(x):valid=False;break
            x=cycle(x)
        if not valid or not good(x):continue
        y=cycle(x)
        if not good(y):continue
        f=model.features(x);g=model.features(y)
        append({j:-v for j,v in f.items()},0)
        delta=dict(g)
        for j,v in f.items():delta[j]=delta.get(j,0)-v
        flip=(x&1)!=(y&1)
        append(delta,-(1 if charge=='every' else int(flip)))
        accepted+=1;flips+=int(flip)
    matrix=csr_matrix((values,cols,ptr),shape=(len(rhs),model.dim))
    result=linprog(np.zeros(model.dim),A_ub=matrix,b_ub=rhs,bounds=model.bounds(),
                   method='highs-ds',options={'time_limit':seconds})
    fit_result={'width':width,'actual_prior_cycles':age,'pattern_length':model.r,
                'position_modulus':model.modulus,'prefix_reference_tracking':model.prefix,
                'charged_for':charge,'variables':model.dim,'accepted_pairs':accepted,
                'free_bit_flips':flips,'inequalities':len(rhs),'status':int(result.status),
                'message':result.message,'finite_sample_feasible_only':bool(result.success),
                'candidate_is_a_verified_rank':False,'exact_LP_refutation':False,
                'seconds':round(time.monotonic()-began,3)}
    if result.success:
        fit_result['floating_max_constraint_violation']=float(np.max(matrix@result.x-np.array(rhs)))
        fit_result['floating_coefficients']=result.x.tolist()
    return fit_result


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-width',type=int,default=16)
    ap.add_argument('--age',type=int,default=0)
    args=ap.parse_args()
    assert 10<=args.max_width<=20 and 0<=args.age<=8
    checked=controls();print(json.dumps({'controls':checked}),flush=True)
    results=[]
    path=Path(__file__).with_name('period-three-prefix-rank-age'+str(args.age)+'.json')
    for r,modulus,prefix in [(2,1,False),(3,3,False),(3,12,False),(2,12,True),(3,12,True),(4,12,True)]:
        for charge in ['every','flip']:
            for width in range(10,args.max_width+1,2):
                result=fit(width,args.age,Model(r,modulus,prefix),charge,20)
                results.append(result)
                print(json.dumps({k:v for k,v in result.items() if k!='floating_coefficients'}),flush=True)
                path.write_text(json.dumps({'untrusted_finite_experiment_only':True,'Lean_verified':False,
                    'C3w_011_proved':False,'full_problem_claim':False,'controls':checked,
                    'results':results},indent=2)+'\n',encoding='utf-8',newline='\n')
                if result['status']!=0:break


if __name__=='__main__':main()
