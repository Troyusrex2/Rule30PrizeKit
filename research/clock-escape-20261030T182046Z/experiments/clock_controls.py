from pathlib import Path
import json
R=Path(__file__).resolve().parent
def G(x):return x^((x<<1)|(x<<2))
quiet=[];excitation=[];quiet_cases=0;excitation_cases=0
for j in range(1,13):
    limit=(j+1)//2;maximum=0
    for x in range(1,1<<(j+1),2):
        initial=(x>>j)&1;a=x
        for t in range(1,limit+1):
            a=G(a)
            if ((a>>j)&1)!=initial:break
        else:raise AssertionError(('quiet',j,x))
        maximum=max(maximum,t);quiet_cases+=1
    assert maximum==limit
    quiet.append(dict(j=j,max_first_change=maximum,bound=limit))
for j in range(1,11):
    i=j+1;limit=(j+1)//2+1;maximum=0
    for low in range(1,1<<i,2):
        for a in [0,1]:
            for b in [0,1]:
                x=low|(a<<(i+1));y=low|(1<<i)|(b<<(i+1))
                for t in range(limit+1):
                    if ((x>>(i+1))&1)!=((y>>(i+1))&1):break
                    x=G(x);y=G(y)
                else:raise AssertionError(('excitation',j,low,a,b))
                maximum=max(maximum,t);excitation_cases+=1
    assert maximum==limit
    excitation.append(dict(first_difference=i,max_first_next_digit=maximum,bound=limit))
rows=[1]
for t in range(32):rows.append(G(rows[-1]))
for j in range(1,65):
    limit=(j+1)//2
    assert all(((rows[t]>>j)&1)==0 for t in range(limit))
    assert (rows[limit]>>j)&1
x,y=1,3
for t in range(128):
    assert ((x>>2)&1)==((y>>2)&1)
    x=G(x);y=G(y)
out=dict(quiet=quiet,quiet_cases=quiet_cases,excitation=excitation,
    excitation_cases=excitation_cases,seed_positions_checked=64,
    excluded_first_digit_control_steps=128,all_passed=True,
    status='Independent arbitrary-precision sanity controls; uniform claims are Lean proofs, not inferred from these ranges.')
(R/'CLOCK_CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['quiet','excitation','status']}))
