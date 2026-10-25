"""Full physical scalar Rule30, independent of the packed candidate search."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent

def update(s):
    if not s:return set()
    result=set()
    for p in range(min(s)-1,max(s)+2):
        left=p-1 in s;center=p in s;right=p+1 in s
        if left != (center or right):result.add(p)
    return result

def start(b,tail):
    return {-1} | ({0} if b else set()) | {-3-i for i in range(5) if (tail>>i)&1}

checks=0;left_checks=0
for tail in range(32):
    rows=[start(False,tail),start(True,tail),start(False,tail^1),start(True,tail^1)]
    for t in range(65):
        delta=rows[0]^rows[1]
        expected={t}|({t-1} if t%2 else set())
        assert delta==expected
        assert (rows[2]^rows[3])==delta
        assert rows[0]^rows[1]^rows[2]^rows[3]==set()
        assert not {p for p in delta if p<0}
        checks+=1;left_checks+=1
        rows=[update(r) for r in rows]

# A missing shielding black cell destroys the same proposed identity.
rows=[set(),{0},{-3},{0,-3}];failure=None
for t in range(10):
    if rows[0]^rows[1]^rows[2]^rows[3]:failure=t;break
    rows=[update(r) for r in rows]
assert failure is not None
proof=json.loads((root/'evidence/Rule30FiniteRectangleResearch/report.json').read_bytes())
assert proof['check']['verdict']=='pass' and proof['check']['replay']=={'constants':72,'ok':True}
result={'pass':True,'independent_scalar_physical_steps':True,'whole_line_controls':checks,
        'left_half_agreement_controls':left_checks,'missing_shield_control_first_failure':failure,
        'all_time_claim_supported_by_Lean_not_by_finite_controls':True,
        'source_sha256':hashlib.sha256((root/'Rule30FiniteRectangleResearch.lean').read_bytes()).hexdigest(),
        'canonical_observer_refuted':False,'full_problem_solved':False}
(root/'rectangle-independent-verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
