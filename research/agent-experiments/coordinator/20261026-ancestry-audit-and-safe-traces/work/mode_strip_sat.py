"""Falsify a fixed-context mode inverse at larger clocks.

SAT witnesses are independently checked literally. UNSAT is only a solver
answer for the stated finite cyclic clock, not a kernel proof or a theorem
for arbitrary older periods.
"""
from pathlib import Path
import hashlib,json,sys,time
r=Path(__file__).resolve().parent
if (r.parent/'temporal-decoder-20261026T1100/solver-deps').exists():
    deps=r.parent/'temporal-decoder-20261026T1100/solver-deps'
else:deps=Path.home()/'Rule30-offload/research/temporal-decoder-20261026/solver-deps'
sys.path.insert(0,str(deps));import z3
reports=[];start=time.monotonic()

def trial(R,width,white=False):
    P=2*R;T=2*P;mask=(1<<T)-1
    solver=z3.Solver();solver.set(timeout=8000,max_memory=1536,random_seed=1319)
    fields=[[z3.BitVec(f'a{a}_{j}',T) for j in range(width)] for a in range(2)]
    modes=[];observations=[]
    for field in fields:
        for j in range(2,width):
            solver.add(z3.RotateRight(field[j],1)==field[j]^(field[j-1]|field[j-2]))
        if white:
            solver.add(z3.RotateRight(field[0],1)==field[0])
            solver.add(z3.RotateRight(field[1],1)==field[1]^field[0])
        g,h,k,l=field[-1],field[-2],field[-3],field[-4]
        solver.add(z3.RotateRight(h,P)==~h,z3.RotateRight(k,R)==~k,z3.RotateRight(l,R)==l)
        q=z3.RotateRight(g,P)^g;S=q|(~k&~l)
        modes.append(q);observations.append(S)
        solver.add(z3.Extract(0,0,g)==0)
    solver.add(observations[0]==observations[1],z3.Extract(0,0,modes[0])!=z3.Extract(0,0,modes[1]))
    t=time.monotonic();answer=solver.check();elapsed=time.monotonic()-t
    report={'R':R,'P':P,'cyclic_time_clock':T,'strip_width_including_g_h':width,
            'white_boundary':white,'canonical_initial_word_required':False,
            'solver_timeout_ms':8000,'status':str(answer),'seconds':round(elapsed,3)}
    if answer==z3.sat:
        model=solver.model();witness=[]
        for field in fields:
            profiles=[model.eval(x,model_completion=True).as_long() for x in field]
            rows=[[x>>t&1 for x in profiles] for t in range(T)]
            for t,row in enumerate(rows):
                for j in range(2,width):
                    assert rows[(t+1)%T][j]==((30>>(4*row[j]+2*row[j-1]+row[j-2]))&1)
                if white:
                    assert rows[(t+1)%T][0]==row[0]
                    assert rows[(t+1)%T][1]==(row[1]^row[0])
                assert rows[(t+P)%T][-2]==1-row[-2]
                assert rows[(t+R)%T][-3]==1-row[-3]
                assert rows[(t+R)%T][-4]==row[-4]
            q=[rows[(t+P)%T][-1]^rows[t][-1] for t in range(T)]
            S=[q[t]|((1-rows[t][-3])&(1-rows[t][-4])) for t in range(T)]
            witness.append({'profiles_oldest_to_newest':profiles,'q':q,'S':S,'initial':rows[0]})
        assert witness[0]['q'][0]!=witness[1]['q'][0] and witness[0]['S']==witness[1]['S']
        report['literal_audit_passed']=True;report['witnesses']=witness
    elif answer==z3.unknown:report['reason_unknown']=solver.reason_unknown()
    return report

for R,width in [(8,6),(8,10),(16,10),(32,10),(16,12),(32,12)]:
    out=trial(R,width);reports.append(out)
    print(json.dumps({k:v for k,v in out.items() if k!='witnesses'}),flush=True)
    (r/'mode-strip-sat.json').write_text(json.dumps({'z3_version':z3.get_version_string(),'reports':reports,
        'Lean_verified':False,'arbitrary_older_periods_not_exhausted':True,
        'uniform_inverse_proved':False,'full_problem_solved':False,
        'seconds':round(time.monotonic()-start,3)},indent=2)+'\n')
assert reports[0]['status']=='sat' and reports[1]['status']=='unsat'
