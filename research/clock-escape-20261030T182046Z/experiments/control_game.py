from pathlib import Path
from collections import deque
import sys,json,time
sys.setrecursionlimit(20000)
R=Path(__file__).resolve().parent;start=time.monotonic();results=[]
for d in [2,3,4]:
    n=d+2;mask=(1<<n)-1
    def step(v,c,h):return (v^(((v<<1)|c)|((v<<2)|(c<<1)|h)))&mask
    states=[(x,y,c,h) for x in range(1<<n) for y in range(1<<n)
            if ((x^y)&1) and (x>>d)==(y>>d) for c in [0,1] for h in [0,1]]
    state_set=set(states);edges={}
    for s in states:
        x,y,c,h=s;a,b=step(x,c,h),step(y,c,h)
        edges[s]=[(a,b,cp,hp) for cp in [0,1] for hp in [0,1]
                  if (not h or cp!=c) and (a,b,cp,hp) in state_set]
    index={};low={};stack=[];on=set();components=[]
    def visit(v):
        index[v]=low[v]=len(index);stack.append(v);on.add(v)
        for w in edges[v]:
            if w not in index:visit(w);low[v]=min(low[v],low[w])
            elif w in on:low[v]=min(low[v],index[w])
        if low[v]==index[v]:
            comp=[]
            while True:
                w=stack.pop();on.remove(w);comp.append(w)
                if w==v:break
            components.append(comp)
    for s in states:
        if s not in index:visit(s)
    recurrent=[c for c in components if len(c)>1 or c[0] in edges[c[0]]]
    witness=None
    for comp in recurrent:
        C=set(comp)
        for s in comp:
            if s[2]!=1:continue
            for v in edges[s]:
                if v not in C:continue
                paths={v:[v]};q=deque([v])
                while q and s not in paths:
                    u=q.popleft()
                    for w in edges[u]:
                        if w in C and w not in paths:paths[w]=paths[u]+[w];q.append(w)
                if s in paths:witness=[s]+paths[s];break
            if witness:break
        if witness:break
    results.append(dict(band_width=d,states=len(states),recurrent_components=len(recurrent),
        cycle_with_c_black=witness))
out=dict(results=results,seconds=time.monotonic()-start,
    interpretation='Controlled inner band with one-step ancestor compatibility. Synthetic cycles are not source-reachable Rule30 counterexamples.')
(R/'CONTROL_GAME.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(results=[dict(width=x['band_width'],cycle_len=None if x['cycle_with_c_black'] is None else len(x['cycle_with_c_black'])-1) for x in results],seconds=out['seconds'])))
