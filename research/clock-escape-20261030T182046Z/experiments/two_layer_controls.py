from pathlib import Path
import json,time
R=Path(__file__).resolve().parent;start=time.monotonic()
def T(x):return x^((x<<1)|(x<<2))
cases=0;depth=[]
for j in range(9):
    bound=(j+1)//2+2;largest=0
    for p in range(1,1<<(j+1),2):
        for a in range(8):
            for b in range(8):
                x=p+(a<<(j+2));y=p+(1<<(j+1))+(b<<(j+2));t=0
                while not ((x^y)&(3<<(j+3))) and t<=bound:
                    x,y=T(x),T(y);t+=1
                assert t<=bound,(j,p,a,b,t)
                largest=max(largest,t);cases+=1
    depth.append(dict(first_difference=j+1,bound=bound,max_observed=largest))
sharp=[]
for n in range(65):
    i=2*n+3;x=1+(1<<i)+(1<<(i+2));y=1+(1<<(i+1))+(1<<(i+2));t=0
    while not ((x^y)>>(i+2)):
        x,y=T(x),T(y);t+=1
        assert t<=n+3
    assert t==n+3
    sharp.append(dict(n=n,first_escape=t,bound=n+3))
out=dict(passed=True,paired_prefixes_up_to_swap=cases,depth=depth,sharp_family_cases=len(sharp),
    seconds=time.monotonic()-start,scope='Independent integer sanity checks. Uniform proofs use actual T in Lean, not these finite checks.')
(R/'TWO_LAYER_CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='depth'}))
