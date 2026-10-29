from clock_graph import graph, ROOT
import json
results=[]
for q in [32,64,128,256,512,1024]:
    r=graph(q,cap=400000,seconds=25)
    results.append(r)
    (ROOT/'LARGER-CLOCK-GRAPHS.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(r),flush=True)
    if not r['complete']:break
