"""Explore the verified five-tail obstruction's compatible front-window lifts.

Numerical exploration only. No observed cycle or residue is a Lean premise.
"""
import time
import numpy as np
from numba import njit
from core import save

@njit
def scan(k,max_steps):
    mask=(np.uint64(1)<<np.uint64(k))-np.uint64(1)
    W=np.uint64(13);bad=np.empty(100000,np.uint64);nb=0
    hist=np.zeros(65,np.int64);maxdelay=-1
    for r in range(max_steps):
        if r%2==1:
            x=W;delay=-1
            for s in range(k):
                if (r+s)%2==0 and x&np.uint64(1)==0:delay=s;break
                x=(x>>np.uint64(1))^(x|(x<<np.uint64(1)))
            if delay<0:
                if nb>=len(bad):return -2,bad,nb,hist,maxdelay
                bad[nb]=r;nb+=1
            else:hist[delay]+=1;maxdelay=max(maxdelay,delay)
        W=(W^((W<<np.uint64(1))|(W<<np.uint64(2)))^np.uint64(1))&mask
        if (r+1)%2==0 and W==13:return r+1,bad[:nb],nb,hist,maxdelay
    return -1,bad[:nb],nb,hist,maxdelay

def control():
    for k in range(4,13):
        w=13&((1<<k)-1);fp=0
        for r in range(100):
            explicit=(w^((w<<1)|(1-fp)|(w<<2)|((1-fp)<<1)|fp))&((1<<k)-1)
            simple=(w^((w<<1)|(w<<2))^1)&((1<<k)-1)
            assert explicit==simple
            w=explicit;fp=1-fp
    return {'explicit_front_steps':900,'all_passed':True}

def main():
    out={'control':control(),'records':[],'full_problem_solved':False};start=time.monotonic()
    for k in range(30,53,2):
        before=time.monotonic();period,bad,nb,hist,delay=scan(k,1<<27)
        row={'width':k,'period':int(period),'bad_count':int(nb),'bad_odd_residues':[int(r) for r in bad],
             'max_certified_postarrival_delay':int(delay),
             'postarrival_delay_counts':{i:int(x) for i,x in enumerate(hist) if x},
             'seconds':round(time.monotonic()-before,3)}
        if period>0:
            assert int(hist.sum())+nb==period//2
            if k==34:assert period==65536 and list(bad)==[61005]
        out['records'].append(row);save('front-lifts.json',out);print(row,flush=True)
        if period<0:break
    out['seconds']=round(time.monotonic()-start,3);save('front-lifts.json',out)

if __name__=='__main__':main()
