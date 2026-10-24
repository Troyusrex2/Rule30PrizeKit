"""Resolve a fixed ordinary arrival in a hard front family, without scanning its orbit."""
import argparse,time
import numpy as np
from numba import njit
from core import phi,save
from front_wide import front_step,first_white,controls

@njit
def state128(initial,steps):
    lo=np.uint64(initial);hi=np.uint64(0);mask=np.uint64(0xffffffffffffffff)
    for _ in range(steps):lo,hi=front_step(lo,hi,mask,mask)
    return lo,hi

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--word',type=int,default=131)
    parser.add_argument('--arrival',type=int,default=32379339);args=parser.parse_args()
    assert args.word&1 and args.arrival%2==1
    start=time.monotonic();out={'word':args.word,'arrival':args.arrival,'width':128,
                              'controls':controls(),'Lean_verified':False,'Q01_counterexample':False}
    lo,hi=state128(args.word,args.arrival);packed=int(lo)|(int(hi)<<64)
    delay=int(first_white(128,np.uint64(lo),np.uint64(hi),args.arrival))
    out['two_limb_seconds']=round(time.monotonic()-start,3)
    # Independent Python arbitrary-precision update, not the compiled limb code.
    a=args.word;mask=(1<<128)-1;before=time.monotonic()
    for _ in range(args.arrival):a=(phi(a)^1)&mask
    assert a==packed
    row=a;scalar_delay=None
    for s in range(128):
        if (args.arrival+s)%2==0 and row&1==0:scalar_delay=s;break
        row=(row>>1)^(row|(row<<1))
    assert delay==(scalar_delay if scalar_delay is not None else -1)
    out.update({'arbitrary_precision_seconds':round(time.monotonic()-before,3),
                'independent_updates_agree':True,'first_even_white_postarrival_delay':scalar_delay,
                'first_even_white_time':args.arrival+scalar_delay if scalar_delay is not None else None,
                'state128_hex':hex(packed),'seconds':round(time.monotonic()-start,3)})
    save(f'hard-front-{args.word}-{args.arrival}.json',out);print(out,flush=True)

if __name__=='__main__':main()
