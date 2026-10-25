"""Independent whole-line pulse evolution and finite weight-space controls."""
from pathlib import Path
import hashlib,json

root=Path(__file__).resolve().parent

def evolve(s,rule):
    if not s:return set()
    return {p for p in range(min(s)-1,max(s)+2)
            if (rule >> (4*(p-1 in s)+2*(p in s)+(p+1 in s)))&1}

def pulse(a):
    return ({8} if a&1 else set()) | ({15} if a&2 else set())

def rows(rule):
    result=[]
    for a in range(4):
        s=pulse(a)
        for _ in range(4):s=evolve(s,rule)
        assert not (s-set(range(4,20)))
        result.append([int(i+4 in s) for i in range(16)])
    return result

before=[[int(i+4 in pulse(a)) for i in range(16)] for a in range(4)]
after=rows(30)

# Independently verify the pointwise mixed derivative used in Lean. A local
# arbitrary Bool^2 score is represented by its four independent coefficients.
for b in [0,1]:
    for i in range(16):
        for table in range(16):
            old=0;new=0
            for a in range(4):
                old ^= (table>>(2*before[a][i]+before[2*b][i]))&1
                new ^= (table>>(2*after[a][i]+after[2*b][i]))&1
            assert old==0
            expected=(((table>>b)^(table>>(2+b)))&1) if i==7 else 0
            assert new==expected

def rank(vectors):
    pivots={}
    for row in vectors:
        while row:
            p=row.bit_length()-1
            if p not in pivots:
                pivots[p]=row
                break
            row ^= pivots[p]
    return len(pivots)

def weight_space(q,rule):
    images=after if rule==30 else rows(rule)
    equations=[]
    for x in range(q):
        for a in range(4):
            for b in range(4):
                row=0
                for i in range(16):
                    oldstate=2*before[a][i]+before[b][i]
                    newstate=2*images[a][i]+images[b][i]
                    if oldstate:row^=1<<(3*((x+i)%q)+oldstate-1)
                    if newstate:row^=1<<(3*q+3*((x+i)%q)+newstate-1)
                equations.append(row)
    r=rank(equations)
    return {'rule':rule,'spatial_period':q,'variables':6*q,
            'equations':len(equations),'rank':r,'nullity':6*q-r}

checks=[weight_space(q,30) for q in range(1,65)]
assert all(c['nullity']==0 for c in checks)
controls=[weight_space(q,150) for q in [1,2,3,4,7]]
assert all(c['nullity']>=2*c['spatial_period'] for c in controls)
result={'pass':True,'independent_whole_line_evolution':True,
        'all_four_patterns_no_black_cells_outside_retained_output':True,
        'mixed_derivative_local_truth_checks':2*16*16,
        'Rule30_periodic_weight_controls':checks,'linear_Rule150_controls':controls,
        'finite_data_are_not_premises_of_Lean_uniform_theorem':True,
        'source_sha256':hashlib.sha256((root/'Rule30WeightedCellResearch.lean').read_bytes()).hexdigest(),
        'full_problem_solved':False}
(root/'weighted-independent-verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'pass':True,'whole_line_patterns':4,'local_truth_checks':1024,
                  'Rule30_weight_periods_checked':64,'linear_controls':5}))
