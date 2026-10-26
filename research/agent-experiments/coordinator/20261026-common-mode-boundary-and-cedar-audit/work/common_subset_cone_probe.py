"""Finite-cone test for a local all-time-Common subset propagation proof."""
from pathlib import Path
import json,time,sys
sys.path.insert(0,r'D:\MWB\Rule30\toolchain\python-research')
import z3

root=Path(__file__).resolve().parent
reports=[]
for H in [1,2,3,4,6,8,12]:
    width=4*H+6;target=2*H+2
    arrays={label:[[z3.Bool(f'{label}_{H}_{t}_{j}') for j in range(width)] for t in range(H+1)] for label in ['a','b','h']}
    a,b,h=[arrays[label] for label in ['a','b','h']]
    d=[[z3.Xor(a[t][j],b[t][j]) for j in range(width)] for t in range(H+1)]
    s=z3.Solver();s.set(timeout=5000,max_memory=1024,random_seed=6748)
    for j in range(width):s.add(z3.Implies(h[0][j],d[0][j]))
    for t in range(H+1):
        for j in range(2*t,width-1):s.add(z3.And(d[t][j],h[t][j+1])==z3.And(h[t][j],d[t][j+1]))
        if t==H:continue
        for j in range(2*(t+1),width):
            for x in [a,b]:s.add(x[t+1][j]==z3.Xor(x[t][j],z3.Or(x[t][j-1],x[t][j-2])))
            s.add(h[t+1][j]==z3.Xor(z3.Xor(h[t][j],z3.And(z3.Not(b[t][j-2]),h[t][j-1])),z3.And(z3.Not(a[t][j-1]),h[t][j-2])))
    s.add(h[1][target],z3.Not(d[1][target]))
    start=time.monotonic();ans=s.check()
    report={'horizon':H,'initial_width':width,'target':target,'status':str(ans),'seconds':time.monotonic()-start}
    if ans==z3.unknown:report['reason']=s.reason_unknown()
    if ans==z3.sat:
        m=s.model();rows={label:[[int(z3.is_true(m.eval(v,model_completion=True))) for v in row] for row in arr] for label,arr in arrays.items()}
        aa,bb,hh=[rows[label] for label in ['a','b','h']]
        dd=[[x^y for x,y in zip(ar,br)] for ar,br in zip(aa,bb)]
        assert all(not hh[0][j] or dd[0][j] for j in range(width))
        for t in range(H+1):
            for j in range(2*t,width-1):assert dd[t][j]*hh[t][j+1]==hh[t][j]*dd[t][j+1]
            if t==H:continue
            for j in range(2*(t+1),width):
                for x in [aa,bb]:assert x[t+1][j]==((30>>(4*x[t][j]+2*x[t][j-1]+x[t][j-2]))&1)
                assert hh[t+1][j]==hh[t][j]^((1-bb[t][j-2])*hh[t][j-1])^((1-aa[t][j-1])*hh[t][j-2])
        assert hh[1][target] and not dd[1][target]
        report.update({'rows':rows,'literal_equations_audited':True,'not_an_all_time_counterexample':True})
    reports.append(report)
    print(json.dumps({k:v for k,v in report.items() if k!='rows'}),flush=True)
    if ans==z3.unsat:break
(root/'common-subset-cone-probe.json').write_text(json.dumps({'reports':reports,
    'scope':'finite interior cones; arbitrary older inputs, not a white-boundary or all-time counterexample'},indent=2)+'\n',encoding='utf-8')
