"""All temporal paths of a short actual strip with two free older inputs."""
from pathlib import Path
from math import gcd
import json
from periodic_driver_probe import sccs
root=Path(__file__).resolve().parent
results=[]
for width in range(4,11):
    mask=(1<<width)-1
    allowed={s for s in range(1<<width) if ((s>>(width-2))&3)!=0}
    adj=[]
    for s in range(1<<width):
        fixed=(s ^ ((s<<1)|(s<<2)))&mask&~3
        adj.append(tuple(fixed|u for u in range(4) if s in allowed and (fixed|u) in allowed))
    live=set(allowed)
    while True:
        nxt={v for v in live if any(w in live for w in adj[v])}
        if nxt==live:break
        live=nxt
    cyclic=[]
    for comp in sccs(adj):
        if len(comp)==1 and comp[0] not in adj[comp[0]]:continue
        members=set(comp);distance={comp[0]:0};todo=[comp[0]]
        while todo:
            v=todo.pop()
            for w in adj[v]:
                if w in members and w not in distance:
                    distance[w]=distance[v]+1;todo.append(w)
        d=0
        for v in comp:
            for w in adj[v]:
                if w in members:d=gcd(d,abs(distance[v]+1-distance[w]))
        labels=[]
        for back in range(1,min(5,width-1)+1):
            slot=width-1-back
            classes={};bad=False
            for v in comp:
                key=distance[v]%d;b=(v>>slot)&1
                if key in classes and classes[key]!=b:bad=True
                classes[key]=b
            two=not bad and all(classes[k]==classes[(k+2)%d] for k in classes)
            labels.append(two)
        cyclic.append({'size':len(comp),'period':d,'two_periodic_outputs_by_distance':labels})
    all_two=[all(c['two_periodic_outputs_by_distance'][b-1] for c in cyclic)
             for b in range(1,min(5,width-1)+1)]
    live_bad=[]
    for b in range(1,min(5,width-1)+1):
        slot=width-1-b;example=None
        for v in live:
            for w in adj[v]:
                for u in adj[w]:
                    if u in live and ((v^u)>>slot)&1:
                        example=[v,w,u];break
                if example:break
            if example:break
        live_bad.append(example)
    result={'width':width,'live_states':len(live),'cyclic_scc_count':len(cyclic),
        'eventually_two_periodic_by_distance':all_two,
        'two_step_counterexample_in_future_live_graph':live_bad,
        'cyclic_components':cyclic}
    results.append(result)
    print(json.dumps({k:v for k,v in result.items() if k not in ['cyclic_components','two_step_counterexample_in_future_live_graph']}),flush=True)
(root/'constant-or-graph.json').write_text(json.dumps({'scope':'two older inputs free every step',
    'results':results},indent=2)+'\n',encoding='utf-8')
