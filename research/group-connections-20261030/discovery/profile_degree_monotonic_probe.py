"""Before evaluation: H3, Newton degree never decreases on any edge pair
reachable from the white root, at the existing q8/16/32 clocks. If refuted,
do not discard terminal nodes or relax the inequality after seeing data.
Only test this candidate; no larger graph is generated.
"""
from pathlib import Path
from collections import Counter
import json
R=Path(__file__).resolve().parent
P=(Path(__file__).resolve().parent/'input/PROFILE-GRAPH.json')
records=[]
for g in json.loads(P.read_text())['graphs']:
    q=g['q'];degrees={}
    for v in {v for pair in g['nodes'] for v in pair}:
        a=[(v>>t)&1 for t in range(q)]
        for j in range(q.bit_length()-1):
            for t in range(q):
                if (t>>j)&1:a[t]^=a[t^(1<<j)]
        degrees[v]=max((i for i,x in enumerate(a) if x),default=-1)
    drops=[{'a':a,'b':b,'degree_a':degrees[a],'degree_b':degrees[b]} for a,b in g['nodes'] if degrees[a]>degrees[b]]
    records.append({'q':q,'pairs':len(g['nodes']),'drops':len(drops),'counterexample':next((d for d in drops if d['degree_a']>1),drops[0] if drops else None),
                    'degree_pairs':{str(k):v for k,v in Counter((degrees[a],degrees[b]) for a,b in g['nodes']).items()}})
(R/'profile-degree-monotonic-result.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items() if k!='degree_pairs'} for x in records]))
