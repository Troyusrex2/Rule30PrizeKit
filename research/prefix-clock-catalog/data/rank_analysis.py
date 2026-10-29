from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parent;g=json.loads((ROOT/'attempt01-g913/RESULTS.json').read_text())['graphs'][-1]
q=g['q'];nodes=g['nodes'];edges=g['edges'];rank={};active=set()
def per2(w):return all(((w>>t)&1)==((w>>((t+2)%q))&1) for t in range(q))
def visit(i):
    if per2(nodes[i][1]):return 0
    if i in rank:return rank[i]
    assert i not in active,'a genuine bad-profile cycle would refute this rank'
    active.add(i);children=[j for j in edges[i] if j is not None]
    assert all(not per2(nodes[j][1]) for j in children)
    r=max((visit(j)+1 for j in children),default=0)
    active.remove(i);rank[i]=r;return r
for i in range(len(nodes)):visit(i)
values=[rank.get(i,0) for i in range(len(nodes))]
result={'q':q,'states':len(nodes),'bad_profile_states':len(rank),'maximum_rank':max(values),'ranks':values,'scope':'computed finite rank, not Lean proof','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'PROFILE-RANK.json').write_text(json.dumps(result,separators=(',',':'))+'\n');print(json.dumps({k:v for k,v in result.items() if k!='ranks'}))
