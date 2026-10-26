from pathlib import Path
import json
r=Path(__file__).resolve().parent;p=json.loads((r/'strip-observer.json').read_bytes())
nodes=set(p['components'][p['reports'][0]['component']]);states=p['states'];edges=p['edges']
same=[];flip=[];patterns=set()
for i in nodes:
    a,b,u,v=states[i];patterns.add(a^b)
    for j,_,_ in edges[i]:
        if j not in nodes:continue
        target=flip if ((a^states[j][0])&1) else same
        target.append((i,j))
out={'recurrent_states':len(nodes),'head_same_edges':len(same),'head_flip_edges':len(flip),
     'difference_patterns':sorted(patterns),'head_not_forced_alternating':bool(same)}
(r/'strip-inspection.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
