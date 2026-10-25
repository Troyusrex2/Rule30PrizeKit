"""A parameterized single-defect family; seek a scalable mechanism, not random fits."""
from pathlib import Path
import json,time
from fractions import Fraction
import feedback_core as core
root=Path(__file__).resolve().parent;start=time.monotonic()
forbidden=['00','11111','010110','1011010']
records=[];best=None;stop=None;unknown=0
indices=list(range(257))+[384,511,512,513,767,1023,1024,1025,1535,2047,2048]
with (root/'delayed-defects.partial.jsonl').open('w',encoding='utf-8') as log:
    for ones in [2,3,4]:
        for j in indices:
            if time.monotonic()-start>230:stop='internal_time_budget';break
            s='01'*j+'0'+'1'*ones;first=0
            allowed=not any(w in s+'01'*8 for w in forbidden)
            if not allowed:continue
            prefix=list(map(int,s));cycle=core.spatial_cycle(prefix,first,cap=80000)
            rec={'j':j,'ones':ones,'free_prefix_bits':s,'tail_first':first,'cycle':cycle}
            records.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
            if 'period' not in cycle:unknown+=1;continue
            if best is None or Fraction(cycle['density'])<Fraction(best['cycle']['density']):
                best=rec;print(json.dumps({'j':j,'ones':ones,'minimum':{k:cycle[k] for k in ['period','black','density','entry_depth']}}),flush=True)
            if 3*cycle['period']>16*cycle['black']:
                stop='generic_Golden_C4_counterexample_candidate';break
        print(json.dumps({'ones_done':ones,'records':len(records),'unknown':unknown,'elapsed_seconds':time.monotonic()-start}),flush=True)
        if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'family':'(01)^j 0 1^r (01)^infinity, r in {2,3,4}, satisfying all four finite word constraints',
     'forbidden_words':forbidden,'records':records,'best':best,'unknown':unknown,
     'stop':stop,'elapsed_seconds':time.monotonic()-start,
     'scope':'Complete-cycle tests for a parameterized arbitrary free-input family. No actual finite-right realizability or universal density assertion.'}
(root/'delayed-defects.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['unknown','stop','elapsed_seconds']}))
