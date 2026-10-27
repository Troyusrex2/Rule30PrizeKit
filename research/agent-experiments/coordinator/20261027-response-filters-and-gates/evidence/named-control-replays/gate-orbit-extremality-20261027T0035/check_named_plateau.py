"""Fixed inherited plateau family only; no new orbit census."""
from pathlib import Path
import json

def D(n):return n ^ ((n>>1)|(n>>2))
def literal(n):
    bits=[(n>>j)&1 for j in range(n.bit_length()+2)]
    return sum((bits[j]^(bits[j+1]|bits[j+2]))<<j
               for j in range(n.bit_length()))
G={1,2,6,10,14}
out=[]
for n in [868,1736,1737]:
    rows=[n]
    for t in range(32):
        assert literal(rows[-1])==D(rows[-1])
        rows.append(D(rows[-1]))
    assert rows[32]==n
    assert all(rows[d]!=n for d in [1,2,4,8,16])
    phases=[]
    for phase in [0,1]:
        orbit=rows[phase:32:2]
        M=max(orbit);j=orbit.index(M)
        shifted=[rows[(phase+2*j+t)%32] for t in range(32)]
        gates=[((r&1)|((r>>1)&1)) if t%2==0 else r&1
               for t,r in enumerate(shifted)]
        phases.append({'phase':phase,'max':M,'max_register':M%16,
                       'max_in_G':M%16 in G,'max_time_from_seed':phase+2*j,
                       'gate_failures_from_max':[t for t,g in enumerate(gates) if not g],
                       'R_orbit':orbit})
    out.append({'seed':n,'D_minimal_period':32,'phases':phases})
result={'status':'PASS; named inherited finite-white plateau only',
        'prior_source':'../even-clock-lifting-20261026T2120/REPORT.md',
        'tested_shortcut':'every nontrivial R-orbit maximum has register outside G',
        'control':out,'alltime_gated_counterexample':False,'new_lean_claim':False}
Path(__file__).with_name('CONTROL.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':result['status'],'controls':[{'seed':v['seed'],'phases':[{k:x[k] for k in ['phase','max','max_register','max_in_G','gate_failures_from_max']} for x in v['phases']]} for v in out]}))
