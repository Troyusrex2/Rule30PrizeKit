"""Minimize the period-28 shortcut counterexample and check scalar reconstruction."""
from pathlib import Path
import json,time
import feedback_core as core
root=Path(__file__).resolve().parent;start=time.monotonic()
rec=json.loads((root/'period-lifting.json').read_text())['counterexample']
prefix=rec['prefix'];first=rec['tail_first'];attempts=0
def bad(p,f):
    global attempts
    attempts+=1;c=core.spatial_cycle(p,f,cap=40000)
    return c if c.get('period') is not None and 28%c['period'] else None
cycle=bad(prefix,first);assert cycle is not None
for chunk in [64,32,16,8,4,2,1]:
    changed=True
    while changed:
        changed=False
        for i in range(len(prefix)-chunk+1):
            p=prefix[:i]+prefix[i+chunk:];c=bad(p,first)
            if c:
                prefix=p;cycle=c;changed=True;break
for i in range(len(prefix)):
    if prefix[i]:
        p=prefix[:];p[i]=0;c=bad(p,first)
        if c:prefix=p;cycle=c
m=len(prefix);mu=2*m;width=mu+4
def f(s):return prefix[s] if s<m else first^((s-m)%2)
columns=[[0]*width,[1 if t%2==0 else f(t//2) for t in range(width)]]
limit=cycle['entry_depth']+3*cycle['period']
for d in range(2,limit+1):
    last,cur=columns[-2:]
    columns.append([cur[(t+1) if t+1<width else mu]^(cur[t]|last[t]) for t in range(width)])
entry=cycle['entry_depth'];p=cycle['period']
assert columns[entry-1]==columns[entry+p-1] and columns[entry]==columns[entry+p]
assert all(columns[d]==columns[d+p] for d in range(entry,limit-p+1))
bits=''.join(str(columns[d][0]) for d in range(entry,entry+p))
assert bits==cycle['cycle_bits']
assert any(columns[d][0]!=columns[d+28][0] for d in range(entry,entry+p))
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'prefix':prefix,'tail_first':first,'cycle':cycle,'attempts':attempts,
     'scalar_columns_checked':len(columns),'scalar_cells_checked':len(columns)*width,
     'elapsed_seconds':time.monotonic()-start,
     'scope':'Exact complete temporal-state cycle and independent scalar recurrence. Arbitrary driver, not actual finite R. Period need not divide 28.'}
(root/'period28-counterexample.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
