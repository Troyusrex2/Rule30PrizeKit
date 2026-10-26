"""One small, targeted falsification test of a ONE-excursion decoder.

This is not a safety-width census and does not test all-time trace equality.
Only the 128 canonical words 1(00|11){0,1}^6 000 are examined.
"""
from pathlib import Path
import json,itertools
root=Path(__file__).parent
table=(0,1,1,1,1,0,0,0)  # index=4*current+2*previous+older
def step(xs):return [table[4*x+2*(xs[i-1] if i else 0)+(xs[i-2] if i>1 else 0)] for i,x in enumerate(xs)]
def orbit(xs):
    out=[xs];x=step(xs)
    while x!=xs:
        out.append(x);x=step(x)
        assert len(out)<=1024
    return out
groups={};witness=None;count=0
for core in ([1,0,0],[1,1,1]):
    for mid in itertools.product((0,1),repeat=6):
        word=core+list(mid)+[0,0,0]
        rows=orbit(word);trace=[x[-1] for x in rows];P=len(rows)
        leave=next(t for t in range(P) if trace[t])
        ret=next(t for t in range(leave+1,leave+P+1) if not trace[t%P] and not trace[(t+1)%P])
        code=tuple(trace[t%P] for t in range(ret+2))
        parent=tuple(rows[t%P][-2] for t in range(ret+2))
        count+=1
        if code in groups:
            old=groups[code]
            if parent[:ret+1]!=old['parent'][:ret+1]:
                witness={'a':old['word'],'b':word,'first_excursion_code':code,
                         'return_time':ret,'parent_a':old['parent'],'parent_b':parent,
                         'first_parent_difference':next(t for t,(a,b) in enumerate(zip(old['parent'],parent)) if a!=b),
                         'a_rows':old['rows'][:ret+2],'b_rows':rows[:ret+2],
                         'full_traces_equal':old['trace']==trace,'whole_orbits':[len(old['rows']),len(rows)]}
                break
        else:groups[code]={'word':word,'parent':parent,'rows':rows,'trace':trace}
    if witness:break
report={'candidate_family':'1(00|11){0,1}^6 000','tested_before_stop':count,'found':witness is not None,'witness':witness,
        'scope':'Only refutes the proposed one-excursion parent decoder if found; not full first-return coding, sink separation, or P1.'}
(root/'first-return-control.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='witness'}))
if witness:print(json.dumps({k:v for k,v in witness.items() if not k.endswith('_rows')}))
