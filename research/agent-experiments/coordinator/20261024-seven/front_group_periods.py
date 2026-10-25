"""Falsify a proposed half-width return-period bound before formalizing it.

F=Phi xor1 agrees with the official front update on complementary bit0/phase.
Finite cycle decomposition below uses every w-bit input, not sampled orbits.
"""
import argparse,time
import numpy as np
from numba import njit
from core import save,phi

@njit
def cycles(w):
    n=1<<w;mask=n-1;seen=np.zeros(n,np.uint8)
    counts=np.zeros(w+1,np.int64);maxperiod=0;witness=0
    for a in range(n):
        if seen[a]:continue
        x=a;length=0
        while not seen[x]:
            seen[x]=1;length+=1;x=(x^((x<<1)|(x<<2))^1)&mask
        assert x==a and length>0 and length&(length-1)==0
        exponent=0;v=length
        while v>1:exponent+=1;v>>=1
        counts[exponent]+=1
        if length>maxperiod:maxperiod=length;witness=a
    return counts,maxperiod,witness

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--max-width',type=int,default=22)
    args=parser.parse_args();out={'map':'Phi xor1','complete_domains':[],
        'finite_experiment_only':True,'Lean_verified':False,'full_problem_solved':False}
    for w in range(1,args.max_width+1):
        start=time.monotonic();counts,maximum,witness=cycles(w)
        assert sum(int(c)*(1<<e) for e,c in enumerate(counts))==1<<w
        x=witness
        for _ in range(int(maximum)):x=(phi(x)^1)&((1<<w)-1)
        assert x==witness
        bound=1<<((w+3)//2)
        row={'width':w,'states':1<<w,'cycle_counts_by_exponent':list(map(int,counts)),
             'maximum_period':int(maximum),'maximum_witness':int(witness),
             'candidate_bound':bound,'candidate_holds':maximum<=bound,
             'seconds':round(time.monotonic()-start,3)}
        out['complete_domains'].append(row);save('front-group-periods.json',out)
        print({k:v for k,v in row.items() if k!='cycle_counts_by_exponent'},flush=True)
        if maximum>bound:break

if __name__=='__main__':main()
