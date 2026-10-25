"""Exact symbolic Boolean tables of the new echo readout; finite diagnostics."""
from pathlib import Path
from collections import Counter
import json,time,random
root=Path(__file__).resolve().parent;start=time.monotonic()
def var_table(j,n):
    size=1<<n;b=1<<j
    out=((1<<b)-1)<<b;width=2*b
    while width<size:out |= out<<width;width*=2
    return out
def phi(a):return a^((a<<1)|(a<<2))
def direct(a,r):
    value=0
    for t in range(r+1):
        if t&r==t:value ^= a>>(2*r-1)&1
        a=phi(a)
    return value
def map_input(q,r,seedlow):
    if not seedlow:return q
    a=1|((q&1)<<1)|((q&1)<<2)
    for k in range(3,2*r-1):a |= ((q>>(k-2))&1)<<k
    return a
rng=random.Random(301636)
records=[];checks=0
for seedlow in [False,True]:
    for r in range(2,10):
        n=2*r-3 if seedlow else 2*r-1
        size=1<<n;ones=(1<<size)-1
        vars=[var_table(j,n) for j in range(n)]
        if seedlow:
            state=[ones,vars[0],vars[0]]+[vars[k-2] for k in range(3,2*r-1)]+[0]
        else:state=vars+[0]
        truth=0
        for t in range(r+1):
            if t&r==t:truth ^= state[2*r-1]
            state=[v^((state[j-1] if j else 0)|(state[j-2] if j>=2 else 0)) for j,v in enumerate(state)]
        for q in ([*range(size)] if n<=7 else [rng.randrange(size) for _ in range(128)]):
            assert (truth>>q&1)==direct(map_input(q,r,seedlow),r)
            checks+=1
        coeff=truth
        for j in range(n):coeff ^= (coeff<<(1<<j))&vars[j]
        counts=Counter();first={};work=coeff
        while work:
            low=work&-work;q=low.bit_length()-1;work ^= low
            degree=q.bit_count();counts[degree]+=1;first.setdefault(degree,q)
        degree=max(counts,default=0);monomial=first.get(degree,0)
        # Independent direct-evolution parity for the selected ANF coefficient.
        parity=0;q=monomial;terms=0
        while True:
            parity ^= direct(map_input(q,r,seedlow),r);terms+=1
            if q==0:break
            q=(q-1)&monomial
        assert parity==1
        records.append({'seedlow':seedlow,'r':r,'free_variables':n,'degree':degree,
                        'monomial_count':sum(counts.values()),'degree_histogram':dict(sorted(counts.items())),
                        'highest_degree_witness_variables':[j for j in range(n) if monomial>>j&1],
                        'independent_mobius_terms':terms,
                        'small_anf_monomial_masks':[q for q in range(size) if coeff>>q&1] if n<=5 else None})
out={'finite_only':True,'full_problem_solved':False,'claim':'Exact finite ANFs; no unbounded degree theorem or computational lower bound.',
     'direct_truth_table_controls':checks,'records':records,'elapsed_seconds':time.monotonic()-start}
(root/'echo-anf.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'controls':checks,'elapsed_seconds':out['elapsed_seconds']}))
for r in records:print(json.dumps({k:r[k] for k in ['seedlow','r','free_variables','degree','monomial_count']}))
