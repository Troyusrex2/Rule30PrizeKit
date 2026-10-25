"""Falsify the uniform spatial-period-28 conjecture before proving any instance."""
from pathlib import Path
import json,random,time
import feedback_core as core
root=Path(__file__).resolve().parent;start=time.monotonic();rng=random.Random(301752)
records=[];counter=None;stop=None;hist={}
for m in [0,1,2,3,4,8,16,32,64,128,256,512]:
    for trial in range(64):
        if time.monotonic()-start>230:stop='internal_time_budget';break
        prefix=[rng.randrange(2) for _ in range(m)];first=rng.randrange(2)
        cycle=core.spatial_cycle(prefix,first,cap=40000)
        rec={'prefix':prefix,'tail_first':first,'cycle':cycle};records.append(rec)
        p=cycle.get('period');hist[str(p)]=hist.get(str(p),0)+1
        if p is not None and 28%p:
            counter=rec;stop='uniform_period_28_counterexample';break
    print(json.dumps({'prefix_length':m,'records':len(records),'period_histogram':hist,'stop':stop}),flush=True)
    if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'rng_seed':301752,'records':records,'period_histogram':hist,'counterexample':counter,
     'stop':stop,'elapsed_seconds':time.monotonic()-start,
     'scope':'Arbitrary eventually alternating drivers, not necessarily realized by finite R. Closed complete temporal-state cycles, not observed output periods.'}
(root/'period-lifting.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'records':len(records),'period_histogram':hist,'stop':stop,'elapsed_seconds':out['elapsed_seconds']}))
