"""Do all-time-looking common linear modes stay pointwise subsets?
This is a finite falsification test, not an all-time assertion.
"""
from pathlib import Path
import argparse,itertools,json
ROOT=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--width',type=int,default=6);p.add_argument('--horizon',type=int,default=128);args=p.parse_args()
width=args.width;T=args.horizon
def step(a):return (a<<2)^((a<<1)|a)
def dstep(a,b,h):return (h<<2)^((~b)&(h<<1))^((~(a<<1))&h)
def common(delta,h):return ((delta<<1)&h)==((h<<1)&delta)
bad=[];survivors=0;tested=0;finite_subset_failures=0;latest_failure=0
for a0,b0 in itertools.combinations(range(1<<width),2):
    delta0=a0^b0;h0=(delta0-1)&delta0
    while h0:
        tested+=1;a,b,h=a0,b0,h0;first_subset=None;end=None
        for t in range(T+1):
            delta=a^b
            if not common(delta,h):end=t;break
            if h&~delta and first_subset is None:first_subset=t
            if t<T:
                assert dstep(a,b,delta)==step(a)^step(b)
                h=dstep(a,b,h);a,b=step(a),step(b)
        if first_subset is not None:finite_subset_failures+=1
        if end is None:
            survivors+=1
            if first_subset is not None:bad.append({'a':a0,'b':b0,'h0':h0,'first_subset_failure':first_subset})
        else:latest_failure=max(latest_failure,end)
        h0=(h0-1)&delta0
out={'width':width,'through_time':T,'nontrivial_modes_tested':tested,'common_survivors':survivors,
     'modes_with_subset_failure_before_common_failure':finite_subset_failures,
     'latest_common_failure':latest_failure,'subset_failure_survivors':bad,
     'finite_only':True,'Lean_verified':False,'unbounded_subset_preservation_proved':False}
(ROOT/f'common-subset-probe-{width}.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
