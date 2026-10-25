from pathlib import Path
import json,random,time
from observer_core import observer
root=Path(__file__).resolve().parent;start=time.monotonic();rng=random.Random(301905)
records=[];stop=None
with (root/'observer-generic.partial.jsonl').open('w',encoding='utf-8') as log:
    for W in range(2,25):
        for trial in range(100):
            if time.monotonic()-start>230:stop='internal_time_budget';break
            K=2*W+1;gap=rng.randrange(1,W+1)
            a=rng.getrandbits(K)|1
            b=(rng.getrandbits(K)>>gap<<gap)|(1<<gap)
            rec=observer(W,0,30,8*W+64,initial_pair=(a,b))
            rec.update(kind='finite_background_pair',trial=trial,A_hex=hex(a),B_hex=hex(b),origin_index=W,left_edge_gap=gap)
            records.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
            if rec['unresolved']:stop='generic_edge_observer_unresolved';break
        print(json.dumps({'W_done':W,'records':len(records),'stop':stop,'elapsed_seconds':time.monotonic()-start}),flush=True)
        if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,'rng_seed':301905,
     'records':records,'stop':stop,'elapsed_seconds':time.monotonic()-start,
     'scope':'Finite initial A/B with different negative-or-zero left edges; exact frozen pair identity and observer checks. No general finite-background theorem.'}
(root/'observer-generic.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'records':len(records),'stop':stop,'elapsed_seconds':out['elapsed_seconds']}))
