from pathlib import Path
import json,time
R=Path(__file__).resolve().parent;start=time.monotonic();out=[];cases=0
def T(x):return x^((x<<1)|(x<<2))
for j in range(9):
    bound=7*((j+1)//2+1);maximum=0
    for p in range(1,1<<(j+1),2):
        for a in range(64):
            for delta in range(1,16,2):
                x=p+(a<<(j+1));y=p+((a^delta)<<(j+1));t=0
                while not ((x^y)&(3<<(j+5))) and t<=bound:
                    x,y=T(x),T(y);t+=1
                assert t<=bound,(j,p,a,delta,t)
                maximum=max(maximum,t);cases+=1
    out.append(dict(first_difference=j+1,max_observed=maximum,proved_bound=bound))
result=dict(passed=True,cases=cases,depths=out,seconds=time.monotonic()-start,
    scope='Independent finite integer sanity checks through first-difference digit9. Uniform all-depth theorem is proved symbolically in Lean, not inferred from these tests.')
(R/'BUDGET_CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in result.items() if k!='depths'}))
