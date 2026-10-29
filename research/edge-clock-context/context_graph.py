"""Can a local drop have arbitrarily deep recurrence-compatible older context?

This is the FULL temporal-word graph, not the white-boundary reachable graph.
Peel vertices with no predecessors; the survivors have arbitrarily deep past.
"""
from collections import deque
from pathlib import Path
import json,time
ROOT=Path(__file__).resolve().parent
def period(x,q):
    h=1
    while h<q:
        if all(((x>>t)^(x>>((t+h)%q)))&1==0 for t in range(q)):return h
        h*=2
    return q
def run(q):
    start=time.monotonic();n=1<<q;mask=n-1
    nexts=[[] for _ in range(n*n)];indeg=[0]*(n*n);drops=[]
    ps=[period(x,q) for x in range(n)]
    for a in range(n):
        for b in range(n):
            d=a|b
            if d.bit_count()%2:continue
            c=0;bit=0
            for t in range(q):c|=bit<<t;bit^=(d>>t)&1
            src=a*n+b
            for c in [c,c^mask]:
                dst=b*n+c;nexts[src].append(dst);indeg[dst]+=1
                if ps[c]<ps[b]:drops.append((src,dst))
    queue=deque(i for i in range(n*n) if indeg[i]==0);depth=[0]*(n*n);removed=set()
    while queue:
        src=queue.popleft();removed.add(src)
        for dst in nexts[src]:
            depth[dst]=max(depth[dst],depth[src]+1);indeg[dst]-=1
            if indeg[dst]==0:queue.append(dst)
    eternal=[(a,b) for a,b in drops if a not in removed]
    result={'q':q,'full_graph_states':n*n,'edges':sum(map(len,nexts)),'drop_edges':len(drops),'drop_edges_with_arbitrarily_deep_older_context':len(eternal),'max_older_edges_into_any_drop':max((depth[a] for a,b in drops if a in removed),default=None),'surviving_states':n*n-len(removed),'example':None,'seconds':time.monotonic()-start,'kernel_verified':False}
    if eternal:
        # Extract one backwards cycle and its finite continuation to a drop.
        src,dst=eternal[0];parents=[[] for _ in range(n*n)]
        for a,outs in enumerate(nexts):
            for b in outs:
                if a not in removed:parents[b].append(a)
        path=[src];seen={src:0};cur=src
        while True:
            cur=parents[cur][0]
            if cur in seen:break
            seen[cur]=len(path);path.append(cur)
        result['example']={'drop_edge':[[src//n,src%n],[dst//n,dst%n]],'backwards_states':[[s//n,s%n] for s in path],'cycle_starts_backwards_index':seen[cur]}
    return result
out=[run(q) for q in [2,4,8]]
(ROOT/'CONTEXT-GRAPH.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
