"""Recheck the Farkas arithmetic without the LP, SMT or elimination code."""
from pathlib import Path
from fractions import Fraction
import json
root=Path(__file__).resolve().parent
def check(system,weights):
    n=system['variables'];sums=[Fraction(0) for _ in range(n)];margin=Fraction(0)
    for i,v in weights:
        if v<0:return False
        for j,c in system['rows'][i].items():sums[int(j)]+=v*c
        margin+=v*system['rhs'][i]
    return all(v==0 for v in sums) and margin>0
reports=[]
for K,m in [(2,1),(3,0),(3,1)]:
    cert=json.loads((root/f'farkas-exact-{K}-{m}.json').read_bytes())
    system=json.loads((root/cert['system_file']).read_bytes())
    weights=[(i,Fraction(s)) for i,s in cert['weights']]
    assert check(system,weights)
    margin=sum((v*system['rhs'][i] for i,v in weights),Fraction())
    assert margin==Fraction(cert['rhs_margin'])
    # Alter a row with positive target RHS; its single-column equation breaks.
    bad=weights.copy();j=next(j for j,(i,v) in enumerate(bad) if system['rhs'][i]>0)
    i,v=bad[j];bad[j]=(i,v+1);assert not check(system,bad)
    bad=weights.copy();i,v=bad[0];bad[0]=(i,-v);assert not check(system,bad)
    reports.append({'context':K,'first_moment':bool(m),'passed':True,'nonzero_weights':len(weights),
                    'columns_checked':system['variables'],'margin':str(margin),
                    'changed_weight_rejected':True,'negative_weight_rejected':True})
out={'passed':True,'reports':reports,'Lean_verified':False,'sink_separation_proved':False,'full_problem_solved':False}
(root/'independent-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
