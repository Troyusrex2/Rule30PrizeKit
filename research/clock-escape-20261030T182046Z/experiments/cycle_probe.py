from pathlib import Path
from collections import deque,Counter
import sys,json,time
R=Path(__file__).resolve().parent;start=time.monotonic();sys.setrecursionlimit(20000)
def sec(w,b):
    out=[]
    for q in reversed(w):out.append(2 if b else (1 if q==2 else 0));b^=q!=0
    return tuple(reversed(out))
results=[]
for P in [2,4,8,16,32]:
    root=(2,)*P;paths={root:(1,)};pending=deque([root]);edges={}
    while pending:
        w=pending.popleft();edges[w]=[]
        if sum(q!=0 for q in w)%2:continue
        for b in [0,1]:
            v=sec(w,b);edges[w].append(v)
            if v not in paths:paths[v]=paths[w]+(b,);pending.append(v)
        assert len(paths)<10000
    index={};low={};stack=[];on=set();components=[]
    def visit(w):
        index[w]=low[w]=len(index);stack.append(w);on.add(w)
        for v in edges[w]:
            if v not in index:visit(v);low[w]=min(low[w],low[v])
            elif v in on:low[w]=min(low[w],index[v])
        if low[w]==index[w]:
            c=[]
            while True:
                v=stack.pop();on.remove(v);c.append(v)
                if v==w:break
            components.append(c)
    visit(root)
    cycles=[c for c in components if len(c)>1 or c[0] in edges[c[0]]]
    results.append(dict(P=P,reachable_states=len(paths),cycle_lengths=sorted(map(len,cycles)),
        cycle_examples=[dict(length=len(c),entry_prefix=list(paths[c[0]]),C_counts=sorted({w.count(2) for w in c})) for c in cycles]))
out=dict(results=results,seconds=time.monotonic()-start,scope='Finite graph analysis at existing P<=32; no assertion for all periods.')
(R/'CYCLE_PROBE.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
