"""Can parity filters of the entire head period recover natural canonical codes?
The code bijection deletes a duplicate after the first 1, or a leading zero
in the period-two core. This tests a new observer certificate template.
"""
from pathlib import Path
import json,time,numpy as np
r=Path(__file__).resolve().parent;begin=time.monotonic();reports=[]
def encode(z,m):
    bits=[(z>>i)&1 for i in range(m)]
    i=next((i for i,x in enumerate(bits) if x),m)
    if i>=m-2:return [0]+bits
    return bits[:i+2]+[bits[i+1]]+bits[i+2:]
def canonical(xs):
    i=next((i for i,x in enumerate(xs) if x),len(xs))
    return i>=len(xs)-2 or (i+3<len(xs) and xs[i+1]==xs[i+2])
for n in range(3,16):
    m=n-1;M=1<<m;P=1<<((2*n-1)//3);mask=(1<<n)-1
    rows=np.array([sum(x<<i for i,x in enumerate(encode(z,m))) for z in range(M)],dtype=np.uint32)
    assert len(set(map(int,rows)))==M
    assert all(canonical(encode(z,m)) for z in range(M))
    initial=rows.copy();basis={};rank=0
    for t in range(P):
        v=int.from_bytes(np.packbits((rows>>(n-1))&1,bitorder='little').tobytes(),'little');coef=1<<t
        while v:
            p=v.bit_length()-1
            if p not in basis:basis[p]=(v,coef);rank+=1;break
            b,c=basis[p];v^=b;coef^=c
        rows=(rows^((rows<<1)|(rows<<2)))&mask
    assert np.array_equal(rows,initial)
    coordinates=[];filters=[]
    for j in range(m):
        v=int.from_bytes(np.packbits((np.arange(M,dtype=np.uint32)>>j)&1,bitorder='little').tobytes(),'little');coef=0
        while v:
            p=v.bit_length()-1
            if p not in basis:break
            b,c=basis[p];v^=b;coef^=c
        if not v:
            coordinates.append(j);filters.append({'coordinate':j,'times':[t for t in range(P) if (coef>>t)&1]})
    report={'width':n,'canonical_rows':M,'working_clock':P,'trace_linear_span_dimension':rank,
            'parity_recoverable_code_coordinates':coordinates,'code_coordinates':m,
            'complete_code_recovered':len(coordinates)==m,'filters':filters}
    reports.append(report)
    print(json.dumps({k:v for k,v in report.items() if k!='filters'}),flush=True)
out={'reports':reports,'finite_widths_only':True,'Lean_verified':False,
     'canonical_observer_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-begin,3)}
(r/'linear-decoder-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'seconds':out['seconds']}),flush=True)
