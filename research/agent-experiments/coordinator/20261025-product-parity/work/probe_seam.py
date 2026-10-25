"""Try to falsify the finite escape deadline U+1; preserve wider caps honestly."""
from pathlib import Path
import json,time
from seam_core import Canonical,reconstruct
root=Path(__file__).resolve().parent;tick=time.monotonic()
maximum_U=128;background=Canonical(5*maximum_U+160)
records=[];failure=None;stop=None
for U in range(1,maximum_U+1):
    for V in range(U):
        if background.center[U]!=background.center[V]:continue
        if time.monotonic()-tick>210:stop='internal_time_budget';break
        r=reconstruct(background,U,V,U+1);records.append(r)
        if r['first_black_depth_beyond_V'] is None:
            failure={'short':r,'extended':reconstruct(background,U,V,4*U+128)}
            stop='short_deadline_refuted';break
    if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'records':records,'failure':failure,'stop':stop,'seconds':time.monotonic()-tick,
     'scope':'Only pairs with matching initial center are tested. A no-escape prefix refutes the proposed finite deadline, not the all-time escape criterion or P1.'}
(root/'seam-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
if failure:
    print(json.dumps({'failure':{k:v for k,v in failure['short'].items() if not k.endswith('_hex')},
      'extended':{k:v for k,v in failure['extended'].items() if not k.endswith('_hex')}}),flush=True)
print(json.dumps({'tested':len(records),'stop':stop,'seconds':out['seconds']}),flush=True)
