"""Complete finite-width orbit audit of a unary rigidity hypothesis.

Every word at each selected width is included, with no time/period cap.
This remains bounded-width evidence, not a uniform theorem.
"""
from pathlib import Path
import json,time
import numpy as np
from numba import njit
r=Path(__file__).resolve().parent;start=time.monotonic()
@njit(cache=False)
def canonical(n,w):
    if n==0:return True
    p=0
    while not (n>>p)&1:p+=1
    d=w-p
    return d<=2 or (d>=4 and ((n>>(p+1))&1)==((n>>(p+2))&1))
@njit(cache=False)
def audit(w):
    size=1<<w;mask=size-1;seen=np.zeros(size,np.uint8)
    good=[];bad=None;cycles=0;maxclock=0;safe_cycles=0;total_safe=0
    for initial in range(size):
        if seen[initial]:continue
        v=initial;safe=True;period=0
        while True:
            assert not seen[v];seen[v]=1
            safe=safe and (v>>(w-3))!=0
            period+=1
            v=(v^((v<<1)|(v<<2)))&mask
            if v==initial:break
        cycles+=1;maxclock=max(maxclock,period)
        if not safe:continue
        safe_cycles+=1;total_safe+=period
        v=initial
        for t in range(period):
            if canonical(v,w):
                good.append(v)
                # Direct scalar iteration: if head does not repeat after8,
                # retain an actual finite-white counterexample.
                z=v
                for _ in range(8):z=(z^((z<<1)|(z<<2)))&mask
                if ((v^z)>>(w-1))&1 and bad is None:bad=(v,period)
            v=(v^((v<<1)|(v<<2)))&mask
    return cycles,maxclock,safe_cycles,total_safe,good,bad
reports=[]
for w in [6,8,12,16,20,24,26]:
    t=time.monotonic();cycles,clock,sc,good,gcanon,bad=audit(w)
    distances=[]
    for n in gcanon:
        p=(n&-n).bit_length()-1;distances.append(w-p)
    out={'width':w,'all_words':1<<w,'complete_orbits':int(cycles),'maximum_period':int(clock),
         'safe_orbits':int(sc),'safe_words':int(good),'safe_canonical_words':[int(x) for x in gcanon],
         'maximum_canonical_source_to_head_width':max(distances,default=0),
         'non_period_eight_counterexample':bad,'seconds':round(time.monotonic()-t,3)}
    reports.append(out);print(json.dumps({k:v for k,v in out.items() if k!='safe_canonical_words'}),flush=True)
    (r/'complete-safe-orbits.json').write_text(json.dumps({'reports':reports,'no_period_or_time_cap':True,
        'finite_widths_only':True,'Lean_verified':False,'uniform_unary_rigidity_proved':False,
        'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)},indent=2)+'\n')
    if bad:break
