from pathlib import Path
import itertools,json
ROOT=Path(__file__).resolve().parent
width=9;maxh=16
def step(a):return (a<<2) ^ ((a<<1)|a)
rows=[]
for a in range(1<<width):
    r=[a]
    for t in range(maxh+1):r.append(step(r[-1]))
    rows.append(r)
results=[]
for horizon in [0,1,2,4,8,16]:
    seen={};bad=[];collisions=0
    for a,b in itertools.combinations(range(1<<width),2):
        key=(rows[a][1]&rows[b][1],tuple(rows[a][t]^rows[b][t] for t in range(1,horizon+2)))
        if key in seen:
            c,d=seen[key];collisions+=1
            if (a^b)!=(c^d) or (a&b)!=(c&d):
                if len(bad)<3:bad.append({'a':a,'b':b,'c':c,'d':d,'previous_delta_equal':(a^b)==(c^d),
                                       'previous_common_equal':(a&b)==(c&d)})
        else:seen[key]=(a,b)
    results.append({'horizon':horizon,'pair_collisions':collisions,'bad_previous_partition':bad})
out={'width':width,'results':results,'finite_only':True,'Lean_verified':False}
(ROOT/'horizon-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
