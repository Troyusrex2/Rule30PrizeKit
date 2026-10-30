"""Falsify stronger arithmetic substitutes before attempting their proof.
P2,4,8,16, prefix length<=10 only. No claim from survival of a test.
"""
from pathlib import Path
import json
R=Path(__file__).resolve().parent
def G(x):return x^((x<<1)|(x<<2))
seen={};raw=None
for n in range(1,4097,2):
    d=G(n)-n
    if d in seen:raw=[seen[d],n,d];break
    seen[d]=n
out=[]
for P in [2,4,8,16]:
    found=None
    for N in range(2,11):
        M=1<<N;seen={}
        for n in range(1,M,2):
            a=n
            for _ in range(P):a=G(a)
            if a%M!=n:continue
            value=a//M
            if value in seen:
                found=dict(N=N,u=seen[value],v=n,tail_at_zero=value);break
            seen[value]=n
        if found:break
    out.append(dict(P=P,zero_tail_collision=found))
(R/'ARITHMETIC_PROBE.json').write_text(json.dumps(dict(displacement_injectivity_counterexample=raw,
    fixed_prefix_zero_tail_tests=out,scope='Bounded falsification of stronger substitutes; not a rigidity theorem.'),indent=2)+'\n')
print(json.dumps(dict(raw=raw,return_tests=out)))
