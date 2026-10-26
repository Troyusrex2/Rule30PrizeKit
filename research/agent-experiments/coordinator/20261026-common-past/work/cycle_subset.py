"""Search a closed right-diagonal prefix, not just a long finite survival.
A terminal SAT witness is independently replayed before any all-time claim.
"""
from pathlib import Path
import json,sys,time
sys.path.insert(0,r'D:\MWB\Rule30\wolfram-local\z3-deps')
import z3
ROOT=Path(__file__).resolve().parent
L=12;W=L+2;mask=(1<<W)-1
records=[]
def mstep(a):return (a^((a<<1)|(a<<2)))&mask
def dstep(a,b,h):return (h^((~(b<<2))&(h<<1))^((~(a<<1))&(h<<2)))&mask
for period in [2,4,8,16,32]:
    solver=z3.Solver();solver.set(timeout=6000,max_memory=1024)
    a=[z3.BitVec('a'+str(t),W) for t in range(period)]
    b=[z3.BitVec('b'+str(t),W) for t in range(period)]
    h=[z3.BitVec('h'+str(t),W) for t in range(period)]
    for t in range(period):
        tn=(t+1)%period;delta=a[t]^b[t]
        solver.add(a[tn]==(a[t]^((a[t]<<1)|(a[t]<<2))))
        solver.add(b[tn]==(b[t]^((b[t]<<1)|(b[t]<<2))))
        solver.add(h[tn]==(h[t]^((~(b[t]<<2))&(h[t]<<1))^((~(a[t]<<1))&(h[t]<<2))))
        solver.add((h[t]&z3.BitVecVal(mask^((1<<L)-1),W))==0)
        solver.add(((delta<<1)&h[t])==((h[t]<<1)&delta))
    solver.add((h[0]&~(a[0]^b[0]))==0)
    solver.add(z3.Or(*[(h[t]&~(a[t]^b[t]))!=0 for t in range(1,period)]))
    start=time.monotonic();status=solver.check()
    result={'period':period,'mode_band':L,'prefix_bits':W,'status':str(status),'seconds':round(time.monotonic()-start,3)}
    if status==z3.sat:
        model=solver.model();av=[model.eval(v).as_long() for v in a];bv=[model.eval(v).as_long() for v in b];hv=[model.eval(v).as_long() for v in h]
        for t in range(period):
            tn=(t+1)%period
            assert mstep(av[t])==av[tn] and mstep(bv[t])==bv[tn] and dstep(av[t],bv[t],hv[t])==hv[tn]
            assert hv[t]>>L==0
            assert (((av[t]^bv[t])<<1)&hv[t])==((hv[t]<<1)&(av[t]^bv[t]))
        result['profiles']={'a':av,'b':bv,'h':hv}
    elif status==z3.unknown:result['reason_unknown']=solver.reason_unknown()
    records.append(result);print(json.dumps(result),flush=True)
    if status==z3.sat:break
out={'records':records,'Lean_verified':False,'full_problem_solved':False}
(ROOT/'cycle-subset.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
