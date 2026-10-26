"""Test a stronger periodic-OR invariant in a relaxed paired actual strip.
Only a finite graph test. Arbitrary older inputs are not white ancestry.
"""
from pathlib import Path
from collections import deque
import json

root = Path(__file__).resolve().parent

def analyze(width):
    size = 1 << width
    mask = size - 1
    source, older = width - 3, width - 4
    def output(s):
        return bool(s & (3 << (width - 2)))
    states = [(a,b) for a in range(size) for b in range(size)
              if (a ^ b) & (1 << source) and not (a ^ b) & (1 << older)
              and output(a) == output(b)]
    index = {v:i for i,v in enumerate(states)}
    adj = []
    for a,b in states:
        aa = (a ^ ((a << 1) | (a << 2))) & mask & ~3
        bb = (b ^ ((b << 1) | (b << 2))) & mask & ~3
        children = [index[(aa|u,bb|v)] for u in range(4) for v in range(4) if (aa|u,bb|v) in index]
        for w in children:
            c,d = states[w]
            for x,y in [(a,c),(b,d)]:
                for j in range(2,width):
                    assert ((y >> j)&1) == ((30 >> (4*((x>>j)&1)+2*((x>>(j-1))&1)+((x>>(j-2))&1)))&1)
        adj.append(children)
    live = set(range(len(states)))
    sizes = [len(live)]
    while True:
        nxt = {v for v in live if any(w in live for w in adj[v])}
        if nxt == live: break
        live = nxt; sizes.append(len(live))
    adjacency = {v: [w for w in adj[v] if w in live] for v in live}
    two = {v:{u for w in adjacency[v] for u in adjacency[w]} for v in live}
    def projection(pair):
        return tuple(s >> (width - 4) for s in pair)
    bad = None
    reach_count = 0
    for v in sorted(live):
        target = projection(states[v])[::-1]
        todo = deque([v]); seen={v}; parent={}
        while todo:
            w=todo.popleft()
            if projection(states[w]) == target:
                path=[w]
                while path[-1] != v: path.append(parent[path[-1]])
                path.reverse()
                full=[v]
                for u,z in zip(path,path[1:]):
                    middle=next(q for q in adjacency[u] if z in adjacency[q])
                    full.extend([middle,z])
                bad={'path': [states[q] for q in full], 'R': len(full)-1,
                     'initial_projection': projection(states[v]),
                     'final_projection': projection(states[w]),
                     'all_edges_literal_audited': True}
                break
            for u in two[w]:
                if u not in seen:seen.add(u); parent[u]=w; todo.append(u)
        reach_count += len(seen)
        if bad:break
    return {'width':width,'pruning_sizes':sizes,'live':len(live),
            'even_swapped_projection_witness':bad,'reached_pairs_before_stop':reach_count,
            'all_inputs_free_in_oldest_two':True,'not_a_white_boundary_counterexample':True}

results=[analyze(w) for w in [5,6,7]]
(root/'periodic-or-pair-probe.json').write_text(json.dumps({'results':results,
    'scope':'finite relaxed graph, no full theorem or finite-white counterexample'},indent=2)+'\n',encoding='utf-8')
for r in results:print(json.dumps({k:v for k,v in r.items() if k!='even_swapped_projection_witness'}|{'witness_R':None if r['even_swapped_projection_witness'] is None else r['even_swapped_projection_witness']['R']}))
