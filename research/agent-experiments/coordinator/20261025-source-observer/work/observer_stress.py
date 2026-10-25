from pathlib import Path
import json,random,time
from observer_core import observer
root=Path(__file__).resolve().parent;start=time.monotonic();rng=random.Random(301904)
records=[];stop=None
with (root/'observer-stress.partial.jsonl').open('w',encoding='utf-8') as log:
    for W in [64,128,256,512,1024,2048,4096]:
        for B in sorted(set([0,1,W//2,W-2,W-1])):
            if time.monotonic()-start>230:stop='internal_time_budget';break
            cap=2*W+32 if W<=1024 else W+256
            rec=observer(W,B,30,cap);rec['kind']='canonical_time_shift';records.append(rec)
            log.write(json.dumps(rec)+'\n');log.flush()
            print(json.dumps({'W':W,'B':B,'recovered':not rec['unresolved'],
                'through':rec['certificate']['observed_through'] if rec['certificate'] else None,
                'rank':rec['rank'],'elapsed_seconds':time.monotonic()-start}),flush=True)
            if rec['unresolved']:stop='canonical_observer_unresolved';break
        if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,'records':records,
     'stop':stop,'elapsed_seconds':time.monotonic()-start,
     'scope':'Multi-output edge-unit recovery on larger actual canonical time-shift fields. Capped failure is unknown, not an all-time counterexample.'}
(root/'observer-stress.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'records':len(records),'stop':stop,'elapsed_seconds':out['elapsed_seconds']}))
