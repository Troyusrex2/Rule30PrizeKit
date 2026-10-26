"""Search a cyclic-background counterexample to local subset preservation.
These are NOT white-boundary Actual histories or prize counterexamples.
"""
from pathlib import Path
import json,time,sys
sys.path.insert(0, r'D:\MWB\Rule30\toolchain\python-research')
from z3 import BitVec, RotateLeft, RotateRight, Solver, sat, unknown

root=Path(__file__).resolve().parent
reports=[]
for width,T in [(3,2),(4,4),(5,4),(6,8),(8,8),(8,16),(10,16)]:
    a=[BitVec(f'a{width}_{T}_{t}',width) for t in range(T)]
    b=[BitVec(f'b{width}_{T}_{t}',width) for t in range(T)]
    h=[BitVec(f'h{width}_{T}_{t}',width) for t in range(T)]
    s=Solver();s.set(timeout=5000,max_memory=1024,random_seed=6747)
    for t in range(T):
        nxt=(t+1)%T;d=a[t]^b[t]
        for x in [a,b]:s.add(x[nxt]==x[t]^(RotateLeft(x[t],1)|RotateLeft(x[t],2)))
        s.add(h[nxt]==h[t]^((~RotateLeft(b[t],2))&RotateLeft(h[t],1))^((~RotateLeft(a[t],1))&RotateLeft(h[t],2)))
        s.add(d&RotateRight(h[t],1)==h[t]&RotateRight(d,1))
    s.add(h[0] & ~(a[0]^b[0])==0,h[0]!=0,h[1]&~(a[1]^b[1])!=0)
    start=time.monotonic();status=s.check()
    report={'width':width,'time_cycle':T,'status':str(status),'seconds':time.monotonic()-start}
    if status==unknown:report['reason']=s.reason_unknown()
    if status==sat:
        model=s.model();aa=[model.eval(x).as_long() for x in a];bb=[model.eval(x).as_long() for x in b];hh=[model.eval(x).as_long() for x in h]
        bit=lambda x,j:(x>>(j%width))&1
        for t in range(T):
            nxt=(t+1)%T
            for j in range(width):
                for x in [aa,bb]:
                    neighborhood=4*bit(x[t],j)+2*bit(x[t],j-1)+bit(x[t],j-2)
                    assert bit(x[nxt],j)==((30>>neighborhood)&1)
                assert bit(hh[nxt],j)==(bit(hh[t],j)^((1^bit(bb[t],j-2))&bit(hh[t],j-1))^((1^bit(aa[t],j-1))&bit(hh[t],j-2)))
                assert (bit(aa[t]^bb[t],j)&bit(hh[t],j+1))==(bit(hh[t],j)&bit(aa[t]^bb[t],j+1))
        assert hh[0]&~(aa[0]^bb[0])==0 and hh[1]&~(aa[1]^bb[1])!=0
        report.update({'a':aa,'b':bb,'h':hh,'all_scalar_equations_audited':True,
                       'initial_subset':True,'subset_fails_at_time_one':True})
    reports.append(report)
    print(json.dumps({k:v for k,v in report.items() if k not in ['a','b','h']}),flush=True)
    if status==sat:break
(root/'common-subset-torus-probe.json').write_text(json.dumps({'reports':reports,
    'scope':'cyclic spatial backgrounds, NOT finite white ancestry or a counterexample to FrontStable'},indent=2)+'\n',encoding='utf-8')
