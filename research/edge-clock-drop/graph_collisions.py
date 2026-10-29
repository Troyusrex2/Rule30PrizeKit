"""Diagnose merges of the complete fixed-clock reachable graphs."""
from pathlib import Path
from collections import defaultdict
import json
ROOT=Path(__file__).resolve().parent
out=[]
for q in [2,4,8,16,32,64]:
    states=[tuple(x) for x in json.loads((ROOT/f'CLOCK-{q}-STATES.json').read_text())]
    parents=defaultdict(list);mask=(1<<q)-1
    for a,b in states:
        d=a|b
        if d.bit_count()%2:continue
        c=0;bit=0
        for t in range(q):c|=bit<<t;bit^=(d>>t)&1
        for new in [c,c^mask]:parents[(b,new)].append((a,b))
    collisions=[{'target':list(s),'parents':[list(p) for p in ps]} for s,ps in parents.items() if len(ps)>1]
    def two_periodic(n):return all(((n>>t)^(n>>((t+2)%q)))&1==0 for t in range(q))
    assert all(two_periodic(x) and two_periodic(y) for s in collisions for x,y in [s['target']])
    out.append({'q':q,'multiple_parent_states':len(collisions),'all_multiple_parent_targets_have_period_dividing_two':True,'collisions':collisions,'kernel_verified':False})
(ROOT/'GRAPH-COLLISIONS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:v for k,v in r.items() if k!='collisions'} for r in out]))
