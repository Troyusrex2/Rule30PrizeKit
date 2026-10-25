"""Check the stronger post-publication half-history control against true gauges."""
from pathlib import Path
import json,time
from common_certificate import certify
from verify_common import replay
root=Path(__file__).resolve().parent;tick=time.monotonic()
def F(s):
    return {p for p in range(min(s)-1,max(s)+2)
       if (p-1 in s)!=((p in s) or (p+1 in s))} if s else set()
data=json.loads((root/'canonical-half-control.json').read_text(encoding='utf-8'))
history=[{0}]
for _ in range(90):history.append(F(history[-1]))
records=[]
for item in data['records']:
    c=item['collision']
    if c is None:continue
    U,V=c['U'],c['V'];a=set(c['A_cells']);b=set(history[V]);z=set(c['B_cells'])
    first_trace=None;first_wedge=None;first_curvature=None;cap=2*U+64
    for t in range(cap+1):
        if first_trace is None and (0 in a)!=(0 in z):first_trace=t
        d=a^b;h=a^z
        for p in range(min(a|b|z)-1,max(a|b|z)+2):
            if first_wedge is None and (((p+1 in d) and (p in h)) != ((p in d) and (p+1 in h))):first_wedge=[t,p]
            if first_curvature is None and ((p in h) and ((p+1 in d)!=(p+1 in h))):first_curvature=[t,p]
        a,b,z=F(a),F(b),F(z)
    assert first_trace is None or first_trace>U
    true=certify(U,V,U)
    if true['edge_forced']:assert replay(true)['recovered']
    records.append({'U':U,'V':V,'edge_prefix':item['edge_prefix'],
       'first_true_A_vs_fake_C_center_difference':first_trace,'through':cap,
       'first_common_field_wedge_violation_of_fake_difference':first_wedge,
       'first_recombination_curvature_of_fake_difference':first_curvature,
       'actual_canonical_pair_N_equals_U_certificate':true,
       'independent_canonical_certificate_passed':true['edge_forced']})
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'records':records,'seconds':time.monotonic()-tick,
     'scope':'A real third trajectory can share a long finite center trace while failing to be a common mode of the two chosen canonical backgrounds. Positive canonical tests are finite only.'}
(root/'canonical-half-followup.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({**out,'records':[{k:v for k,v in r.items() if k!='actual_canonical_pair_N_equals_U_certificate'} for r in records]}),flush=True)
