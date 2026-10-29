from pathlib import Path
import json,time
from pivot_probe import simulate
ROOT=Path(__file__).resolve().parent
start=time.monotonic();K=134;states=simulate(130,K)
c=[(r>>K)&1 for r in states];first=None;checked=0
for s in range(129):
    if time.monotonic()-start>10:raise TimeoutError('fixed cap')
    if not c[s]:continue
    fresh=c[s+1]*((states[s+1]>>(K+1))&1)
    if not fresh:continue
    checked+=1
    det=c[s]*c[s+2]-c[s+1]*c[s+1]
    if det==0:
        first={'offset':s,'center_triple':c[s:s+3],'right_neighbor_at_source':(states[s+1]>>(K+1))&1,
               'fresh_source':fresh,'det_parent':c[s],'det_child':det}
        break
result={'status':'shift_uniform_integer_repair_refuted' if first else 'not_refuted_in_fixed_range',
        'first_counterexample':first,'eligible_borders_checked':checked,'seconds':time.monotonic()-start,
        'scope':'Exact finite computation; leading-border-only claim is unchanged'}
(ROOT/'shifted-integer-result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
