"""Explicit finite cubic filters in Newton differences of the head trace."""
from pathlib import Path
import itertools,json,time,numpy as np
r=Path(__file__).resolve().parent;START=time.monotonic();reports=[]
def encode(z,m):
    xs=[(z>>i)&1 for i in range(m)];i=next((i for i,x in enumerate(xs) if x),m)
    return [0]+xs if i>=m-2 else xs[:i+2]+[xs[i+1]]+xs[i+2:]
def reduce(v,c,basis):
    while v:
        p=v.bit_length()-1
        if p not in basis:break
        b,d=basis[p];v^=b;c^=d
    return v,c
for n in range(4,11):
    M=1<<(n-1);P=1<<((2*n-1)//3)
    rows=np.array([sum(x<<i for i,x in enumerate(encode(z,n-1))) for z in range(M)],dtype=np.uint32)
    initial=rows.copy();newton=[]
    for t in range(P):
        newton.append(int.from_bytes(np.packbits((rows>>(n-1))&1,bitorder='little').tobytes(),'little'))
        rows=(rows^((rows<<1)|(rows<<2)))&((1<<n)-1)
    assert np.array_equal(rows,initial)
    for bit in [1<<k for k in range(P.bit_length()-1)]:
        for i in range(P):
            if i&bit:newton[i]^=newton[i^bit]
    variables=[i for i in range(1,P) if newton[i]] # d0 is unnecessary for an older bit.
    target=int.from_bytes(np.packbits((initial>>(n-2))&1,bitorder='little').tobytes(),'little')
    basis={};terms=[];residual=target;coef=0
    for degree in range(4):
        for monomial in itertools.combinations(variables,degree):
            v=(1<<M)-1
            for k in monomial:v&=newton[k]
            index=len(terms);terms.append(monomial);v,c=reduce(v,1<<index,basis)
            if v:basis[v.bit_length()-1]=(v,c)
        residual,coef=reduce(target,0,basis)
        if not residual:break
    assert not residual,n
    polynomial=[terms[i] for i in range(len(terms)) if (coef>>i)&1]
    # Independent literal trajectories and the binomial-subset definition.
    literal_cells=0
    for z in range(M):
        row=encode(z,n-1);wanted=row[-2];trace=[]
        for t in range(P):
            trace.append(row[-1]);old=row
            row=[(30>>(4*x+2*(old[j-1] if j else 0)+(old[j-2] if j>=2 else 0)))&1 for j,x in enumerate(old)]
            literal_cells+=n
        used={k for monomial in polynomial for k in monomial}
        d={k:sum(trace[i] for i in range(k+1) if i&k==i)%2 for k in used}
        value=0
        for monomial in polynomial:
            product=1
            for k in monomial:product&=d[k]
            value^=product
        assert value==wanted,(n,z)
    report={'width':n,'working_clock':P,'target':'canonical penultimate raw bit',
            'degree':degree,'terms':polynomial,'term_count':len(polynomial),
            'literal_cells_checked':literal_cells,'all_canonical_rows_checked':M}
    reports.append(report)
    print(json.dumps({k:v for k,v in report.items() if k!='terms'}|{'first_terms':polynomial[:16]}),flush=True)
out={'reports':reports,'passed':True,'finite_widths_only':True,'Lean_verified':False,
     'uniform_decoder_proved':False,'canonical_observer_proved':False,'full_problem_solved':False,
     'seconds':round(time.monotonic()-START,3)}
(r/'newton-decoder-filters.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
