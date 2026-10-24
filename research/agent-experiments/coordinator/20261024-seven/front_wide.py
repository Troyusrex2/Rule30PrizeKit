"""Two-limb front-cycle exploration with independent arbitrary-integer controls."""
import argparse,random,time
import numpy as np
from numba import njit
from core import phi,save

U=np.uint64
@njit(inline='always')
def front_step(lo,hi,lowmask,highmask):
    nh=hi^((hi<<U(1))|(lo>>U(63))|(hi<<U(2))|(lo>>U(62)))
    nl=lo^((lo<<U(1))|(lo<<U(2)))^U(1)
    return nl&lowmask,nh&highmask

@njit(inline='always')
def first_white(k,lo,hi,r):
    for s in range(k):
        if (r+s)%2==0 and lo&U(1)==0:return s
        nl=((lo>>U(1))|(hi<<U(63)))^(lo|(lo<<U(1)))
        nh=(hi>>U(1))^(hi|(hi<<U(1))|(lo>>U(63)))
        lo,hi=nl,nh
    return -1

@njit
def scan(k,initial,max_steps):
    lowmask=U(0xffffffffffffffff) if k>=64 else (U(1)<<U(k))-U(1)
    highmask=U(0) if k<=64 else (U(0xffffffffffffffff) if k==128 else (U(1)<<U(k-64))-U(1))
    lo=U(initial)&lowmask;hi=U(0);origin=lo;bad=0;first=-1
    for r in range(max_steps):
        if r%2==1 and first_white(k,lo,hi,r)<0:
            bad+=1
            if first<0:first=r
        lo,hi=front_step(lo,hi,lowmask,highmask)
        if (r+1)%2==0 and lo==origin and hi==0:return r+1,bad,first
    return -1,bad,first

def controls():
    rng=random.Random(307028);stepcases=sigcases=0
    for k in (16,46,62,64,65,72,96,128):
        mask=(1<<k)-1;lm=U(mask&((1<<64)-1));hm=U(mask>>64)
        for _ in range(32):
            a=rng.getrandbits(k)
            lo,hi=front_step(U(a&((1<<64)-1)),U(a>>64),lm,hm)
            assert int(lo)|(int(hi)<<64)==(phi(a)^1)&mask;stepcases+=1
            for r in (0,1):
                got=first_white(k,U(a&((1<<64)-1)),U(a>>64),r)
                b=a;want=-1
                for s in range(k):
                    if (r+s)%2==0 and b&1==0:want=s;break
                    b=(b>>1)^(b|(b<<1))
                assert got==want;sigcases+=1
    for k,p,b in [(34,65536,1),(46,2097152,0)]:
        period,bad,first=scan(k,13,1<<22);assert period==p and bad==b
    return {'wide_step_cases':stepcases,'wide_signature_cases':sigcases,'known_cycle_controls':2,'all_passed':True}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--word',type=int,default=131)
    parser.add_argument('--widths',type=int,nargs='+',default=[64,66,68,70,72])
    parser.add_argument('--max-period',type=int,default=1<<30);args=parser.parse_args()
    out={'word':args.word,'controls':controls(),'records':[],'finite_experiment_only':True,
         'max_steps_per_scan':args.max_period,'full_problem_solved':False}
    for k in args.widths:
        before=time.monotonic();period,bad,first=scan(k,args.word,args.max_period)
        row={'width':k,'complete_orbit':period>0,'period':int(period),
             'bad_count_on_completed_segment':int(bad),'first_bad_odd_residue':int(first),
             'seconds':round(time.monotonic()-before,3)}
        out['records'].append(row);save(f'front-wide-{args.word}.json',out);print(row,flush=True)
        if period>0 and bad==0:break

if __name__=='__main__':main()
