"""Seek an all-future nonwhite obstruction by finite-time background merging."""
from pathlib import Path
import json,time,sys
sys.path.insert(0,r'D:\MWB\Rule30\toolchain\python-research')
from z3 import BitVec,RotateLeft,RotateRight,Solver,sat,unknown
root=Path(__file__).resolve().parent;reports=[]
for width,T in [(4,2),(6,4),(8,4),(8,8),(10,8),(12,12)]:
    a=[BitVec(f'a{width}_{T}_{t}',width) for t in range(T+1)]
    b=[BitVec(f'b{width}_{T}_{t}',width) for t in range(T+1)]
    h=[BitVec(f'h{width}_{T}_{t}',width) for t in range(T+1)]
    s=Solver();s.set(timeout=5000,max_memory=1024,random_seed=6750)
    for t in range(T+1):
        d=a[t]^b[t];s.add(d&RotateRight(h[t],1)==h[t]&RotateRight(d,1))
        if t==T:continue
        for x in [a,b]:s.add(x[t+1]==x[t]^(RotateLeft(x[t],1)|RotateLeft(x[t],2)))
        s.add(h[t+1]==h[t]^((~RotateLeft(b[t],2))&RotateLeft(h[t],1))^((~RotateLeft(a[t],1))&RotateLeft(h[t],2)))
    s.add(h[0]&~(a[0]^b[0])==0,h[0]!=0,a[T]==b[T],h[T]!=0)
    start=time.monotonic();ans=s.check();r={'width':width,'horizon':T,'status':str(ans),'seconds':time.monotonic()-start}
    if ans==unknown:r['reason']=s.reason_unknown()
    if ans==sat:
        m=s.model();aa=[m.eval(x).as_long() for x in a];bb=[m.eval(x).as_long() for x in b];hh=[m.eval(x).as_long() for x in h]
        bit=lambda x,j:(x>>(j%width))&1
        for t in range(T+1):
            for j in range(width):
                assert bit(aa[t]^bb[t],j)*bit(hh[t],j+1)==bit(hh[t],j)*bit(aa[t]^bb[t],j+1)
                if t==T:continue
                for x in [aa,bb]:assert bit(x[t+1],j)==((30>>(4*bit(x[t],j)+2*bit(x[t],j-1)+bit(x[t],j-2)))&1)
                assert bit(hh[t+1],j)==bit(hh[t],j)^((1^bit(bb[t],j-2))*bit(hh[t],j-1))^((1^bit(aa[t],j-1))*bit(hh[t],j-2))
        assert hh[0]&~(aa[0]^bb[0])==0 and aa[T]==bb[T] and hh[T]!=0
        r.update({'a':aa,'b':bb,'h':hh,'literal_audit':True,'future_Common_follows_from_equal_actual_backgrounds':True})
    reports.append(r);print(json.dumps({k:v for k,v in r.items() if k not in ['a','b','h']}),flush=True)
    if ans==sat:break
(root/'common-subset-coalescence-probe.json').write_text(json.dumps({'reports':reports,
    'scope':'cyclic spatial backgrounds; no finite white boundary'},indent=2)+'\n',encoding='utf-8')
