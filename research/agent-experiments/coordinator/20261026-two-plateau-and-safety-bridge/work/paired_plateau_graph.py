"""Two all-time actual strips with saturated newest OR and older anti/period masks."""
from pathlib import Path
from math import gcd
import json
from periodic_driver_probe import sccs
root=Path(__file__).resolve().parent
results=[]
for width in [5,6,7]:
    size=1<<width;mask=size-1;source=width-3;older=source-1
    singles={s for s in range(size) if (s>>(width-2))&3}
    states=[(a,b) for a in singles for b in singles
            if ((a^b)>>source)&1 and not (((a^b)>>older)&1)]
    index={s:i for i,s in enumerate(states)};adj=[]
    for a,b in states:
        fa=(a^((a<<1)|(a<<2)))&mask&~3
        fb=(b^((b<<1)|(b<<2)))&mask&~3
        children=[]
        for ua in range(4):
            for ub in range(4):
                pair=(fa|ua,fb|ub)
                if pair in index:children.append(index[pair])
        adj.append(tuple(children))
    live=set(range(len(states)));rounds=[]
    while True:
        nxt={v for v in live if any(w in live for w in adj[v])}
        rounds.append(len(nxt))
        if nxt==live:break
        live=nxt
    cyclic=[]
    for comp in sccs(adj):
        if len(comp)==1 and comp[0] not in adj[comp[0]]:continue
        members=set(comp);dist={comp[0]:0};todo=[comp[0]]
        while todo:
            v=todo.pop()
            for w in adj[v]:
                if w in members and w not in dist:dist[w]=dist[v]+1;todo.append(w)
        d=0
        for v in comp:
            for w in adj[v]:
                if w in members:d=gcd(d,abs(dist[v]+1-dist[w]))
        classes={};bad=False
        for v in comp:
            key=dist[v]%d;bit=(states[v][0]>>source)&1
            if key in classes and classes[key]!=bit:bad=True
            classes[key]=bit
        two=not bad and all(classes[k]==classes[(k+2)%d] for k in classes)
        cyclic.append({'size':len(comp),'period':d,'source_two_periodic':two})
    bad=None
    for v in live:
        for w in adj[v]:
            for u in adj[w]:
                if u in live and ((states[v][0]^states[u][0])>>source)&1:
                    bad=[states[v],states[w],states[u]];break
            if bad:break
        if bad:break
    # A true R-shifted pair has first(R) = second(0), with no period premise
    # at all on the free older profiles. Test every even path, not just cycles.
    two_edges={v:{u for w in adj[v] for u in adj[w] if u in live} for v in live}
    even_return=None;even_swapped_top=None;even_projected_swap=None;reachability_count=0
    for v in live:
        seen={v};todo=[v]
        while todo:
            w=todo.pop()
            for u in two_edges[w]:
                if u not in seen:seen.add(u);todo.append(u)
        reachability_count+=len(seen)
        targets=[w for w in seen if states[w][0]==states[v][1]]
        if targets and even_return is None:even_return=[states[v],states[targets[0]]]
        swapped=[w for w in targets if (states[w][1]>>(width-4))==(states[v][0]>>(width-4))]
        if swapped and even_swapped_top is None:even_swapped_top=[states[v],states[swapped[0]]]
        projected=[w for w in seen if
            states[w][0]>>(width-4)==states[v][1]>>(width-4) and
            states[w][1]>>(width-4)==states[v][0]>>(width-4)]
        if projected and even_projected_swap is None:even_projected_swap=[states[v],states[projected[0]]]
    result={'width':width,'states':len(states),'live':len(live),'trim_round_sizes':rounds,
            'cyclic_components':cyclic,'all_cyclic_components_source_two_periodic':all(c['source_two_periodic'] for c in cyclic),
            'live_two_step_source_counterexample':bad,'even_reachability_pairs':reachability_count,
            'even_path_first_to_second_return_example':even_return,
            'even_path_with_swapped_top_four_example':even_swapped_top,
            'even_path_swapping_projected_top_four_example':even_projected_swap}
    results.append(result)
    print(json.dumps({k:v for k,v in result.items() if k!='cyclic_components'}),flush=True)
(root/'paired-plateau-graph.json').write_text(json.dumps({'results':results,
    'scope':'two relaxed older-input strips; not yet a Lean theorem'},indent=2)+'\n',encoding='utf-8')
