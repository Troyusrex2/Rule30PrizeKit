"""Try to prove the learned reject state by a simple temporal separation.
Find a counterexample if that proposed inductive invariant is too weak.
"""
from functools import lru_cache
from pathlib import Path
import itertools,json
ROOT=Path(__file__).resolve().parent
def integral(g,i,P):
    mask=(1<<P)-1;x=g;s=1
    while s<P:x^=x<<s;s*=2
    return ((x<<1)&mask)^(mask if i else 0)
@lru_cache(maxsize=None)
def outputs(u,v,P):
    u2=u|(u<<P);v2=v|(v<<P);g=u2|v2
    return tuple((v2,integral(g,i,2*P)) for i in [0,1])
def separated(u,v,up,vp,P):
    a={x|y for x,y in outputs(u,v,P)}
    b={x|y for x,y in outputs(up,vp,P)}
    return not a&b
reports=[]
for P in [2,4,8]:
    mask=(1<<P)-1
    possible=[]
    for u,v in itertools.product(range(1<<P),repeat=2):
        nxt=(v>>1)|((v&1)<<(P-1));dv=nxt^v
        if u&~dv==0:possible.append((u,v))
    bad=None;checked=0
    for (u,v),(up,vp) in itertools.product(possible,repeat=2):
        if not separated(u,v,up,vp,P):continue
        checked+=1
        for ai,(a0,a1) in enumerate(outputs(u,v,P)):
            for bi,(b0,b1) in enumerate(outputs(up,vp,P)):
                if not separated(a0,a1,b0,b1,2*P):
                    bad={'u':u,'v':v,'up':up,'vp':vp,'initial_next':[ai,bi],
                         'next_profiles':[a0,a1,b0,b1]};break
            if bad:break
        if bad:break
    reports.append({'period':P,'locally_right_admissible_states':len(possible),
                    'separated_pairs_checked':checked,'counterexample_to_simple_invariant':bad})
    if bad:break
out={'reports':reports,'Lean_verified':False,'unbounded_separation_proved':False}
(ROOT/'separation-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
