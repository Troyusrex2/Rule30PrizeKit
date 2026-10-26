"""Control: drop actual evolution of b and seek a periodic bounded D-only mode."""
from pathlib import Path
import json,sys,time
sys.path.insert(0,r'D:\MWB\Rule30\wolfram-local\z3-deps')
import z3
root=Path(__file__).resolve().parent;started=time.monotonic();results=[]
def orbit(L):
    a=1;mask=(1<<(L+1))-1;rows=[]
    while not rows or a!=1:
        rows.append(a);a=(a^((a<<1)|(a<<2)))&mask
    return rows
for L in range(2,7):
    aa=orbit(L);T=2*len(aa)
    b=[[z3.Bool(f'b_{t}_{j}') for j in range(L+1)] for t in range(T)]
    h=[[z3.Bool(f'h_{t}_{j}') for j in range(L)] for t in range(T)]
    solver=z3.Solver();solver.set(timeout=20000)
    solver.add(z3.Or(h[0]))
    for t in range(T):
        solver.add(z3.Not(b[t][0]))
        for j in range(L+2):
            hj=h[t][j] if j<L else z3.BoolVal(False)
            c=(z3.Not(b[t][j-2]) if j>=2 else z3.BoolVal(True))
            r=z3.BoolVal(not(aa[t%len(aa)]>>(j-1)&1)) if j>=1 else z3.BoolVal(True)
            lhs=h[(t+1)%T][j] if j<L else z3.BoolVal(False)
            rhs=z3.Xor(z3.Xor(hj,z3.And(c,h[t][j-1]) if j>=1 and j-1<L else False),
                       z3.And(r,h[t][j-2]) if j>=2 and j-2<L else False)
            solver.add(lhs==rhs)
    before=time.monotonic();verdict=solver.check();record={'L':L,'period':T,'verdict':str(verdict),'seconds':time.monotonic()-before}
    if verdict==z3.sat:
        m=solver.model();bv=[sum(int(z3.is_true(m.eval(v,model_completion=True)))<<j for j,v in enumerate(row)) for row in b]
        hv=[sum(int(z3.is_true(m.eval(v,model_completion=True)))<<j for j,v in enumerate(row)) for row in h]
        for t in range(T):
            a=aa[t%len(aa)];B=bv[t];H=hv[t]
            nxt=H^((H<<1)&~(B<<2))^((H<<2)&~(a<<1))
            assert nxt==hv[(t+1)%T]
        failures=[t for t in range(T) if ((bv[t]^((bv[t]<<1)|(bv[t]<<2)))&((1<<(L+1))-1))!=bv[(t+1)%T]]
        record.update(b_controls=bv,h_modes=hv,b_is_actual=False,b_evolution_failures=failures)
        assert failures
    results.append(record);print(json.dumps(record),flush=True)
    if verdict==z3.sat:break
out={'finite_solver_control_only':True,'Lean_verified':False,'W_imposed':False,'b_evolution_imposed':False,
     'z3_version':z3.get_version_string(),'records':results,'seconds':time.monotonic()-started}
(root/'free-b-control.json').write_text(json.dumps(out,indent=2)+'\n')
