"""Test whether complete front certificates extend to arbitrary short tails.

A nonempty bad set is a failure of this bounded certificate, not Q01.
"""
import argparse,time
import numpy as np
from numba import njit
from core import save

@njit
def scan(k,initial,max_steps):
    mask=(np.uint64(1)<<np.uint64(k))-np.uint64(1)
    W=np.uint64(initial)&mask;origin=W;bad=0;firstbad=-1
    for r in range(max_steps):
        if r%2==1:
            x=W;found=False
            for s in range(k):
                if (r+s)%2==0 and x&np.uint64(1)==0:found=True;break
                x=(x>>np.uint64(1))^(x|(x<<np.uint64(1)))
            if not found:
                bad+=1
                if firstbad<0:firstbad=r
        W=(W^((W<<np.uint64(1))|(W<<np.uint64(2)))^np.uint64(1))&mask
        if (r+1)%2==0 and W==origin:return r+1,bad,firstbad
    return -1,bad,firstbad

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--max-word',type=int,default=127)
    args=parser.parse_args();filename='front-family.json' if args.max_word==127 else f'front-family-{args.max_word}.json'
    out={'records':[],'finite_experiments_only':True,'full_problem_solved':False};start=time.monotonic()
    for initial in range(1,args.max_word+1,2):
        attempts=[];complete=False
        for k in (16,24,32,40,48,56,62):
            before=time.monotonic();period,bad,first=scan(k,initial,1<<27)
            attempt={'width':k,'period':int(period),'bad_count':int(bad),
                     'first_bad_odd_residue':int(first),'seconds':round(time.monotonic()-before,3)}
            attempts.append(attempt)
            if period>0 and bad==0:complete=True;break
            if period<0:break
        row={'initial_tail_word':initial,'complete_certificate_found':complete,'attempts':attempts}
        out['records'].append(row);out['seconds']=round(time.monotonic()-start,3)
        save(filename,out);print({'initial':initial,'found':complete,'last':attempts[-1]},flush=True)

if __name__=='__main__':main()
