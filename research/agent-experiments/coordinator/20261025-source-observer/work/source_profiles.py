"""Canonical phase-aware echo tests, with exact finite differences as controls."""
from pathlib import Path
import json,random,time
root=Path(__file__).resolve().parent;start=time.monotonic()
R=128;T=512;mask=(1<<(2*R+1))-1
rows=[1]
for _ in range(T+R+2):
    a=rows[-1];rows.append((a^((a<<1)|(a<<2)))&mask)
def b(r,t):
    if r==0:return 1
    a=rows[t];return (a>>(2*r)&1)*(1^(a>>(2*r-1)&1))
def submasks(r):
    u=r
    while True:
        yield u
        if not u:break
        u=(u-1)&r
def C(r,t):
    out=0
    for u in submasks(r):out^=b(r,t+u)
    return out
controls=0
for r in range(33):
    for t in range(33):
        a=[b(r,t+u) for u in range(r+1)]
        for _ in range(r):a=[x^y for x,y in zip(a,a[1:])]
        assert C(r,t)==a[0];controls+=1
pairs=[]
for r in range(R+1):
    for t in range(0,T,2):
        if C(r,t)!=C(r,t+1):
            pairs.append({'r':r,'even_phase':t,'C_even':C(r,t),'C_odd':C(r,t+1)})
            break
first=min(pairs,key=lambda x:(x['even_phase'],x['r'])) if pairs else None
# Full finite-prefix phase signatures, retaining the mandatory parity bit.
signatures={};aliases=[]
for t in range(T):
    sig=(t%2,tuple(C(r,t) for r in range(33)))
    nxt=tuple(C(r,t+1) for r in range(9))
    if sig in signatures and signatures[sig][1]!=nxt:
        aliases.append({'first_phase':signatures[sig][0],'second_phase':t,
                        'different_output_coordinates':[r for r,(a,b) in enumerate(zip(signatures[sig][1],nxt)) if a!=b]})
    signatures.setdefault(sig,(t,nxt))
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
 'canonical_seed':1,'right_prefix_bits':2*R+1,'r_cap':R,'time_cap':T,
 'independent_difference_controls':controls,
 'even_odd_profile_duplicate_counterexamples':pairs,'first_pair_counterexample':first,
 'parity_augmented_33_coordinate_aliases':aliases,
 'scope':'Canonical finite prefix tests only. No infinite projection closure, clock recovery, center nonperiodicity or generic-state result follows from absence of aliases.',
 'elapsed_seconds':time.monotonic()-start}
(root/'source-profiles.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'first_pair_counterexample':first,'coordinates_with_pair_failure':len(pairs),
 'augmented_aliases':aliases[:3],'controls':controls,'seconds':out['elapsed_seconds']}))
