"""Cheap falsification of the narrower handoff claim; existing P<=32 only."""
from pathlib import Path
from collections import deque
import json,time
R=Path(__file__).resolve().parent;start=time.monotonic();results=[]
def sec(w,b):
    out=[]
    for q in reversed(w):out.append(2 if b else (1 if q==2 else 0));b^=q!=0
    return tuple(reversed(out))
def primitive(w):
    for d in range(1,len(w)+1):
        if len(w)%d==0 and w==w[:d]*(len(w)//d):return d
def step(x):return x^((x<<1)|(x<<2))
for P in [2,4,8,16,32]:
    root=(2,)*P;paths={root:(1,)};q=deque([root]);bad=[];proper=0
    while q:
        w=q.popleft();bits=paths[w];n=len(bits);x=sum(b<<i for i,b in enumerate(bits));d=primitive(w)
        if d<P:
            proper+=1;y=x
            for _ in range(d):y=step(y)
            if (y^x)&((1<<n)-1):bad.append(dict(n=n,prefix=x,word=''.join('ABC'[i] for i in w),proposed_period=d))
        if sum(i!=0 for i in w)%2:continue
        for b in [0,1]:
            v=sec(w,b)
            if v not in paths:paths[v]=bits+(b,);q.append(v)
    results.append(dict(P=P,states=len(paths),proper_power_states=proper,counterexamples=bad))
out=dict(results=results,seconds=time.monotonic()-start,
    scope='One first-reaching prefix per vertex in existing P<=32 graphs. No proof for all prefixes or all P.')
(R/'PERIOD_REFLECTION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(states=sum(x['states'] for x in results),counterexamples=sum(len(x['counterexamples']) for x in results),seconds=out['seconds'])))
