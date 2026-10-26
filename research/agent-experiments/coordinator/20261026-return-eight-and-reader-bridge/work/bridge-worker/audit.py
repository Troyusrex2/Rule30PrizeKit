"""Independent literal-neighborhood validation of the small certificate data."""
from pathlib import Path
import json,hashlib
root=Path(__file__).parent
product=json.loads((root/'product.json').read_text())
states=[tuple(x) for x in product['states']];edges=product['edges']
# Literal Rule30 truth table, indexed as (current, nearest older, older).
rule={(0,0,0):0,(0,0,1):1,(0,1,0):1,(0,1,1):1,
      (1,0,0):1,(1,0,1):0,(1,1,0):0,(1,1,1):0}
def F(xs):return [rule[x,(xs[i-1] if i else 0),(xs[i-2] if i>1 else 0)] for i,x in enumerate(xs)]
paths={0:([],[])}
for i,edges_i in enumerate(edges):
    assert i in paths
    a,b=paths[i]
    for k,n in enumerate(edges_i):
        if n is not None and n not in paths:paths[n]=(a+[k//2],b+[k%2])
checks=0
for i,(a,b) in paths.items():
    expected=[]
    for x in [a,b]:
        p=r=0
        for t in range(9):
            p|=(x[-1] if x else 0)<<t
            r|=(x[-2] if len(x)>1 else 0)<<t
            y=F(x);checks+=len(x);x=y
        expected.extend([p,r])
    assert expected==list(states[i][3:]),(i,expected,states[i])
reset=json.loads((root/'first-return-control.json').read_text())['witness']
ra,rb=[reset['a']],[reset['b']]
for t in range(7):ra.append(F(ra[-1]));rb.append(F(rb[-1]))
assert [x[-1] for x in ra]==[x[-1] for x in rb]==[0,0,0,1,0,1,0,0]
assert ra[6][-3:]==rb[6][-3:]==[0,0,0]
assert ra[2][-2]==0 and rb[2][-2]==1
assert all(ra[t]==reset['a_rows'][t] and rb[t]==reset['b_rows'][t] for t in range(8))
report={'passed':True,'product_states':len(states),'literal_cell_updates':checks,
        'reset_rows':16,'parent_disagreement_time':2,'pair_full_trace_equality_claimed':False,
        'lean_source_sha256':hashlib.sha256((root/'PrizeSafetyBridge.lean').read_bytes()).hexdigest()}
(root/'independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
