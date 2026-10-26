from pathlib import Path
from collections import deque
import json
from periodic_driver_probe import graph, sccs

ROOT=Path(__file__).resolve().parent

def shortest_paths(adj, members, root, reverse=False):
    edges={v:[] for v in members}
    for v in members:
        for w in adj[v]:
            if w in members:
                edges[w if reverse else v].append(v if reverse else w)
    parents={root:None};todo=deque([root])
    while todo:
        v=todo.popleft()
        for w in edges[v]:
            if w not in parents:parents[w]=v;todo.append(w)
    assert len(parents)==len(members)
    return parents

def path_to(parent, node):
    result=[node]
    while parent[result[-1]] is not None:result.append(parent[result[-1]])
    return result

def record(nodes, adj, labels, width):
    return {'nodes':nodes,'outer_bits':[adj[v].index(w) for v,w in zip(nodes,nodes[1:])],
            'outputs':[labels[v] for v in nodes[:-1]],'length':len(nodes)-1}

results=[]
for text in ['110','1011','1100']:
    word=tuple(map(int,text));width=10;adj,labels=graph(word,width)
    found=None
    for component in sorted(sccs(adj),key=len,reverse=True):
        members=set(component)
        if len(members)<2:continue
        root=min(members);forward=shortest_paths(adj,members,root)
        backward=shortest_paths(adj,members,root,True)
        loops=[]
        for v in sorted(members):
            for w in set(adj[v]):
                if w not in members:continue
                nodes=list(reversed(path_to(forward,v)))+path_to(backward,w)
                assert nodes[0]==nodes[-1]==root
                outputs=[labels[n] for n in nodes[:-1]]
                for old_nodes,old_outputs in loops:
                    if outputs+old_outputs!=old_outputs+outputs:
                        found=(record(old_nodes,adj,labels,width),record(nodes,adj,labels,width))
                        break
                if found:break
                loops.append((nodes,outputs))
            if found:break
        if found:break
    assert found is not None,text
    a,b=found
    pq=a['outputs']+b['outputs'];qp=b['outputs']+a['outputs']
    assert len(pq)==len(qp) and pq!=qp
    result={'driver':text,'width':width,'common_base':a['nodes'][0],
            'loop_a':a,'loop_b':b,'equal_block_length':len(pq),
            'first_differing_output':next(i for i,(x,y) in enumerate(zip(pq,qp)) if x!=y),
            'scope':'free outside input, no finite initial condition or all-width claim'}
    results.append(result)
    print(f'{text}: exact noncommuting loops {a["length"]} and {b["length"]}; equal blocks length {len(pq)}')
(ROOT/'periodic-driver-witnesses.json').write_text(json.dumps({'results':results},indent=2)+'\n',encoding='utf-8')
