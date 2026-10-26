from pathlib import Path
from collections import deque
import json
root=Path(__file__).resolve().parent
width=6;size=64;mask=63;source=3;older=2
single={s for s in range(size) if (s>>4)&3}
states=[(a,b) for a in single for b in single if ((a^b)>>3)&1 and not (((a^b)>>2)&1)]
index={s:i for i,s in enumerate(states)};adj=[]
for a,b in states:
    fa=(a^((a<<1)|(a<<2)))&mask&~3;fb=(b^((b<<1)|(b<<2)))&mask&~3
    adj.append([index[(fa|u,fb|v)] for u in range(4) for v in range(4) if (fa|u,fb|v) in index])
live=set(range(len(states)));rounds=[len(live)]
while True:
    nxt={v for v in live if any(w in live for w in adj[v])};rounds.append(len(nxt))
    if nxt==live:break
    live=nxt
bad_gate=[states[v] for v in live if ((states[v][0]>>1)&1) and not ((states[v][0]>>2)&1)]
def project(v):
    a,b=states[v]
    return (a>>2,b>>2)
edges={}
def add(a,b):
    edges.setdefault(a,set()).add(b);edges.setdefault(b,set()).add(a)
for v in live:
    p=project(v);add(p,(p[1],p[0]))
    for w in adj[v]:
        if w in live:add(p,project(w))
colors={};conflict=None
for p in edges:
    if p in colors:continue
    colors[p]=0;todo=deque([p])
    while todo:
        q=todo.popleft()
        for s in edges[q]:
            if s not in colors:colors[s]=1-colors[q];todo.append(s)
            elif colors[s]==colors[q]:conflict=[q,s]
# Specific simple candidate: hA xor hB xor kA.
def phase(s):
    a,b=s
    return ((a>>4)^(b>>4)^(a>>3))&1
phase_bad=[(states[v],states[w]) for v in live for w in adj[v] if w in live and phase(states[v])==phase(states[w])]
result={'live_states':len(live),'round_sizes':rounds,'older_gate_bad_examples':bad_gate,
        'projected_phase_coloring_conflict':conflict,'projected_colors':[{'a':a,'b':b,'color':c} for (a,b),c in colors.items()],
        'simple_phase_nonflipping_edges':phase_bad,
        'all_live_states':[states[v] for v in sorted(live)]}
full_edges={v:set() for v in live}
for v in live:
    for w in adj[v]:
        if w in live:full_edges[v].add(w);full_edges[w].add(v)
    for w in live:
        if project(w)==tuple(reversed(project(v))):
            full_edges[v].add(w);full_edges[w].add(v)
full_colors={};full_conflict=None
for v in live:
    if v in full_colors:continue
    full_colors[v]=0;todo=deque([v])
    while todo:
        w=todo.popleft()
        for u in full_edges[w]:
            if u not in full_colors:full_colors[u]=1-full_colors[w];todo.append(u)
            elif full_colors[u]==full_colors[w]:full_conflict=[states[u],states[w]]
result['full_phase_coloring_conflict']=full_conflict
result['full_phase_colors']=[{'state':states[v],'color':c} for v,c in full_colors.items()]
(root/'plateau-phase-probe.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'live_states':len(live),'round_sizes':rounds,
    'projected_coloring_possible':conflict is None,'full_coloring_possible':full_conflict is None,
    'simple_phase_failed_edge_count':len(phase_bad)}))
