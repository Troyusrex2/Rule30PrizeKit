"""Registered before evaluation: test top Newton moment vanishing, q>=8.

H1: every white-root profile has even total weight (top Newton coefficient0).
H2: its even-tick parity is0 (next-to-top coefficient0).
Only existing q8/16/32 graphs, no larger census. A failed identity is not
repaired by deleting terminal nodes: finite white-root prefixes may end there.
"""
from pathlib import Path
from collections import Counter
import json
R=Path(__file__).resolve().parent
P=(Path(__file__).resolve().parent/'input/PROFILE-GRAPH.json')
data=json.loads(P.read_text());records=[]
for g in data['graphs']:
    q=g['q']
    if q<8:continue
    values={v for pair in g['nodes'] for v in pair};degrees=Counter();bad1=bad2=None
    emask=sum(1<<t for t in range(0,q,2))
    for v in sorted(values):
        a=[(v>>t)&1 for t in range(q)]
        for j in range(q.bit_length()-1):
            for t in range(q):
                if (t>>j)&1:a[t]^=a[t^(1<<j)]
        degrees[max((i for i,x in enumerate(a) if x),default=-1)]+=1
        assert a[-1]==(v.bit_count()%2)
        assert a[-2]==((v&emask).bit_count()%2)
        if a[-1] and bad1 is None:bad1=v
        if a[-2] and bad2 is None:bad2=v
    records.append({'q':q,'profiles':len(values),'newton_degrees':dict(sorted(degrees.items())),
                    'total_parity_counterexample':bad1,'even_tick_counterexample':bad2})
(R/'profile-newton-result.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records))
