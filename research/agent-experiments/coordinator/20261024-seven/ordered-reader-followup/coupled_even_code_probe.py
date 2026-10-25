"""Compare coupled right halves with the constructive even-spatial decoder.

Finite prefixes only: a short even-code prefix is never called finite support.
"""
from functools import lru_cache
import time
from core import save
from empty_right_absorption import step

def even_code(free):
    @lru_cache(None)
    def pair(m,k):
        if m==0:return 1,0
        if m==1:return 1,(free[k] if k<len(free) else 0)
        e,o=pair(m-1,k);ep,op=pair(m-2,k);en,_=pair(m-1,k+1)
        return o^(e|ep),en^(o|op)
    return sum(pair(2*d+2,0)[0]<<d for d in range(len(free)))

def packed_run(row,t):
    for _ in range(t):row=(row>>1)^(row|(row<<1))
    return row

def decode(u,n):
    row=0;free=[]
    for d in range(n):
        row|=(1^(packed_run(row,2*d)&1))<<(2*d)
        row|=((u>>d)&1)<<(2*d+1)
        free.append(packed_run(row,2*d+1)&1)
    return free

def forbidden(free):
    for i in range(len(free)):
        if i>=1 and free[i-1:i+1]==[0,0]:return {'end':i,'word':'00'}
        if i>=4 and free[i-4:i+1]==[1]*5:return {'end':i,'word':'11111'}
    return None

def main():
    start=time.monotonic();n=128;out={'free_bit_horizon':n,'coupled':[],'finite_even_inputs':[],
           'Lean_verified':False,'finite_support_inferred_from_prefix':False,'full_problem_solved':False}
    for R in [0,1,2,3,5,17,31,495]:
        x=R;free=[]
        for t in range(2*n):
            x=step(x,t)
            if t%2==0:free.append(1^(x&1))
        assert len(free)==n and forbidden(free) is None
        code=even_code(free);assert decode(code,n)==free
        row={'right_half':R,'even_code_prefix_hex':hex(code),'last_black_even_index':code.bit_length()-1,
             'black_even_counts':{str(k):(code&((1<<k)-1)).bit_count() for k in [32,64,96,128]}}
        out['coupled'].append(row);print(row,flush=True)
    for u in range(32):
        free=decode(u,n);assert even_code(free)==u
        row={'finite_even_input':u,'first_golden_violation':forbidden(free),
             'free_first64':''.join(map(str,free[:64]))}
        out['finite_even_inputs'].append(row)
    out['seconds']=round(time.monotonic()-start,3);save('coupled-even-code-probe.json',out)
    print({'seconds':out['seconds'],'finite_even_inputs_surviving_golden_prefix':[
        r['finite_even_input'] for r in out['finite_even_inputs'] if r['first_golden_violation'] is None]},flush=True)

if __name__=='__main__':main()
