"""Inspect odd-coordinate tails of the forced row for finite even inputs.

Finite profiles are not eventual-periodicity or infinite-support proofs.
"""
import random,time
from core import save
from zero_tail_rank import step
from coupled_even_code_probe import decode

def main():
    rng=random.Random(302457);records=[];n=1024;start=time.monotonic()
    inputs=list(range(16))+[rng.getrandbits(32) for _ in range(16)]
    for u in inputs:
        R=[];Rm=[];free=[];odd=[]
        for d in range(n):
            R,Rm=step(R,Rm,1);odd.append(R[-1])
            base,_=step(R,Rm,0);s=((u>>d)&1)^base[-1]
            R,Rm=step(R,Rm,s);assert R[-1]==((u>>d)&1);free.append(s)
        assert free[:32]==decode(u,32)
        last_zero=max((i for i,b in enumerate(odd) if not b),default=None)
        periods=[p for p in range(1,65) if all(odd[i]==odd[i-p] for i in range(n-256+p,n))]
        records.append({'input':u,'odd_prefix_length':n,'odd_last_zero':last_zero,
                        'odd_zero_count_last256':odd[-256:].count(0),
                        'odd_suffix256_periods_le64':periods,
                        'free_last128':''.join(map(str,free[-128:]))})
    out={'records':records,'odd_tail_periodicity_proved':False,'Lean_verified':False,
         'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
    save('finite-even-tail-profile.json',out)
    print({'records':len(records),'seconds':out['seconds'],
           'last_odd_zero_sample':[r['odd_last_zero'] for r in records[:8]]},flush=True)

if __name__=='__main__':main()
