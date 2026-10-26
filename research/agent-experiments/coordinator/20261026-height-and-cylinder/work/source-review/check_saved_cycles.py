"""Read only the two existing strip controls; no search or graph expansion."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
source=Path('D:/MWB/Rule30/cedar-d3-batch-20261026T183637Z/integration/free_strip_safety.json')
data=json.loads(source.read_bytes());results=[]
for name in ['bad_cycle','power_two_bad_cycle']:
    xs=data[name]['newest_bits'];P=len(xs)
    assert P==len(data[name]['states_with_wrap'])-1 and any(not x for x in xs) and any(xs)
    safe=all(xs[t] or xs[(t+1)%P] for t in range(P))
    no11011=all([xs[(t+k)%P] for k in range(5)]!=[1,1,0,1,1] for t in range(P))
    zeros=[t for t,x in enumerate(xs) if not x]
    gaps=[(zeros[(i+1)%len(zeros)]-t)%P or P for i,t in enumerate(zeros)]
    R=max(gaps)-1
    clusters=[]
    boundaries=[i for i,g in enumerate(gaps) if g>2]
    if boundaries:
        for i,start in enumerate(boundaries):
            end=boundaries[(i+1)%len(boundaries)]
            clusters.append((end-start)%len(zeros) or len(zeros))
    assert safe and no11011 and all(n>=2 for n in clusters)
    assert 2*P<=(R+3)*len(zeros)
    results.append({'name':name,'period':P,'zero_count':len(zeros),'maximum_one_run':R,'cyclic_zero_cluster_sizes':clusters,'safe':safe,'no11011':no11011,'density_tradeoff_left':2*P,'density_tradeoff_right':(R+3)*len(zeros),'inequality_holds':True})
(root/'saved-cycle-check.json').write_text(json.dumps({'source_path':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'new_search':False,'results':results},indent=2)+'\n',encoding='utf-8')
print(json.dumps(results))
