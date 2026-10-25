"""Search for compact unobservable modes in exact pair-difference fields.

SAT witnesses get independent packed and row-space checks. UNSAT is recorded
only as solver output, never as Lean verification or an unbounded theorem.
"""
from pathlib import Path
import json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root.parent.parent/'z3-deps'))
import z3
from observer_core import observer,advance
start=time.monotonic();records=[]
for W,N in [(4,6),(4,12),(6,10),(6,20),(8,14),(8,28),(12,24),(12,40),(16,48)]:
    if time.monotonic()-start>220:break
    K=2*W+1;offset=N+3;bits=K+2*offset
    a0,b0,h0=z3.BitVecs('a0 b0 h0',K)
    a,b,h=[z3.ZeroExt(bits-K,v)<<offset for v in (a0,b0,h0)]
    solver=z3.SolverFor('QF_BV');solver.set(timeout=20000,max_memory=1536)
    solver.add(z3.Extract(0,0,a0)==1,z3.Extract(0,0,b0)==0,z3.Extract(0,0,h0)==1)
    for t in range(N+1):
        solver.add(z3.Extract(offset+W,offset+W,h)==0)
        if t==N:break
        an,bn,hn=z3.BitVecs('a_'+str(t+1)+' b_'+str(t+1)+' h_'+str(t+1),bits)
        solver.add(an==((a<<1)^(a|z3.LShR(a,1))),
                   bn==((b<<1)^(b|z3.LShR(b,1))),
                   hn==((h<<1)^(h&~z3.LShR(b,1))^(z3.LShR(h,1)&~a)))
        a,b,h=an,bn,hn
    tick=time.monotonic();answer=solver.check()
    r={'W':W,'N':N,'solver':z3.get_version_string(),'verdict':str(answer),
       'solve_seconds':time.monotonic()-tick,'Lean_verified':False}
    if answer==z3.sat:
        m=solver.model();av,bv,hv=[m.eval(v).as_long() for v in (a0,b0,h0)]
        a,b,h=[v<<offset for v in (av,bv,hv)];mask=(1<<bits)-1
        assert av&1 and not bv&1 and hv&1
        for t in range(N+1):
            assert not (h>>(offset+W)&1)
            a,b,h=advance(a,30)&mask,advance(b,30)&mask,((h<<1)^(h&~(b>>1))^((h>>1)&~a))&mask
        ob=observer(W,0,30,N,initial_pair=(av,bv));assert ob['unresolved']
        extended=observer(W,0,30,12*W+96,initial_pair=(av,bv))
        r.update(witness={'A_hex':hex(av),'B_hex':hex(bv),'H_hex':hex(hv)},
                 independently_checked=True,observer_at_N=ob,extended_observer=extended)
    elif answer==z3.unknown:r['reason_unknown']=solver.reason_unknown()
    records.append(r)
    print(json.dumps(r),flush=True)
    (root/'observer-smt.json').write_text(json.dumps({'finite_only':True,'full_problem_solved':False,
       'records':records,'seconds':time.monotonic()-start},indent=2)+'\n',encoding='utf-8')
