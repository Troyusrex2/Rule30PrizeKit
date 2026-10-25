"""Falsify the tempting common-field recovery deadline N=U.

This is a specific bound test, not evidence of unbounded termination.
"""
from pathlib import Path
import json,time
from common_certificate import certify
root=Path(__file__).resolve().parent;tick=time.monotonic();records=[];stop=None
for U in range(1,41):
    for V in range(U):
        if time.monotonic()-tick>200:stop='internal_time_budget';break
        cert=certify(U,V,U)
        records.append({k:v for k,v in cert.items() if k!='rows'})
        if not cert['edge_forced']:
            stop='N_equals_U_false'
            (root/'deadline-failure.json').write_text(json.dumps(cert,indent=2)+'\n',encoding='utf-8')
            controls=[]
            for N in [U+1,2*U,4*U+32]:
                later=certify(U,V,N);controls.append(later)
                if later['edge_forced']:break
            (root/'deadline-recovery.json').write_text(json.dumps(controls,indent=2)+'\n',encoding='utf-8')
            print(json.dumps({'failure':records[-1],'later':[{k:v for k,v in c.items() if k!='rows'} for c in controls]}),flush=True)
            break
    if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'stop':stop,'records':records,'seconds':time.monotonic()-tick,
     'scope':'A failed finite sparse contraction refutes the proposed algorithmic deadline, not physical trace separation or P1. Failure is not full row-space non-recovery.'}
(root/'deadline-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'tested':len(records),'stop':stop,'seconds':out['seconds']}),flush=True)
