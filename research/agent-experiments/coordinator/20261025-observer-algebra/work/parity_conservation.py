"""Exact F2 cyclic-density constraints; no unbounded conclusion from a census."""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent;start=time.monotonic()
widths=range(1,11);bases={m:{} for m in widths};counts={};records=[]
def phi_ring(a,L):
    mask=(1<<L)-1
    left=((a<<1)|(a>>(L-1)))&mask
    right=(a>>1)|((a&1)<<(L-1))
    return left^(a|right)
def pattern_parity(a,L,m):
    ext=0
    for i in range((m+L-2)//L+1):ext|=a<<(i*L)
    out=0;mask=(1<<m)-1
    for p in range(L):out^=1<<((ext>>p)&mask)
    return out
def insert(basis,row):
    while row:
        p=row.bit_length()-1
        if p in basis:row^=basis[p]
        else:basis[p]=row;return
for L in range(1,17):
    for a in range(1<<L):
        b=a
        for _ in range(4):b=phi_ring(b,L)
        for m in widths:
            # Once only coboundaries/constants remain, additional constraints
            # cannot remove them; stop work for that width.
            if len(bases[m])==(1<<(m-1)):continue
            row=pattern_parity(a,L,m)^pattern_parity(b,L,m)
            insert(bases[m],row)
    state={'ring_length':L,'density_nullities':{str(m):(1<<m)-len(bases[m]) for m in widths},
           'expected_trivial_nullities':{str(m):1<<(m-1) for m in widths},
           'seconds':time.monotonic()-start}
    records.append(state);print(json.dumps(state),flush=True)
    if all(len(bases[m])==(1<<(m-1)) for m in widths):break
    if time.monotonic()-start>220:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'coefficient_field':'F2','steps':4,'records':records,
     'final_bases':{str(m):{str(k):hex(v) for k,v in b.items()} for m,b in bases.items()},
     'seconds':time.monotonic()-start,
     'scope':'Finite cyclic constraints suffice to rule out extra F2 conserved densities only at the listed window widths. No arbitrary-width theorem follows.'}
(root/'parity-conservation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
