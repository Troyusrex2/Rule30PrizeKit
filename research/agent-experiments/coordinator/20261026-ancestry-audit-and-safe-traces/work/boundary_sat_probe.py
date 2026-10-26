"""Search actual finite white histories, not only free-input strips."""
from pathlib import Path
import json,sys,time
r=Path(__file__).resolve().parent
deps=Path.home()/'Rule30-offload/research/temporal-decoder-20261026/solver-deps'
if not deps.exists():deps=r.parent/'temporal-decoder-20261026T1100/solver-deps'
sys.path.insert(0,str(deps));import z3
C=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]]
start=time.monotonic();reports=[]

def canonical(solver,field):
    state=z3.IntVal(0)
    for x in field+[z3.BitVecVal(0,field[0].size())]:
        bit=z3.Extract(0,0,x)==1
        state=z3.Sum([z3.If(state==i,z3.If(bit,row[1],row[0]),0) for i,row in enumerate(C)])
    solver.add(z3.Or(*[state==i for i in [0,1,2,3,5]]))

def trial(kind,P,width):
    T=2*P;s=z3.Solver();s.set(timeout=8000,max_memory=1536,random_seed=1341)
    histories=[[z3.BitVec(f'a{a}_{j}',T) for j in range(width)] for a in range(2 if kind=='mode' else 1)]
    obs=[];modes=[]
    for field in histories:
        s.add(z3.RotateRight(field[0],1)==field[0])
        s.add(z3.RotateRight(field[1],1)==field[1]^field[0])
        for j in range(2,width):s.add(z3.RotateRight(field[j],1)==field[j]^(field[j-1]|field[j-2]))
        if kind=='mode':
            g,h,k,l=field[-1],field[-2],field[-3],field[-4]
            s.add(z3.RotateRight(h,P)==~h,z3.RotateRight(k,P)==k)
            canonical(s,field)
            q=z3.RotateRight(g,P)^g;S=q|(~k&~l);obs.append(S);modes.append(q)
        else:
            s.add(z3.RotateRight(field[-1],P)==field[-1],z3.RotateRight(field[-2],P)!=field[-2])
    if kind=='mode':s.add(obs[0]==obs[1],z3.Extract(0,0,modes[0])!=z3.Extract(0,0,modes[1]))
    t=time.monotonic();ans=s.check();out={'kind':kind,'P':P,'cyclic_clock':T,'width':width,
      'white_boundary':True,'canonical_plus_white_head':kind=='mode','solver_timeout_ms':8000,
      'status':str(ans),'seconds':round(time.monotonic()-t,3)}
    if ans==z3.sat:
        model=s.model();witness=[]
        for field in histories:
            values=[model.eval(x,model_completion=True).as_long() for x in field]
            rows=[[x>>t&1 for x in values] for t in range(T)]
            for t,row in enumerate(rows):
                expected=[row[0],row[1]^row[0]]+[(30>>(4*row[j]+2*row[j-1]+row[j-2]))&1 for j in range(2,width)]
                assert rows[(t+1)%T]==expected
            if kind=='mode':
                state=0
                for b in rows[0]+[0]:state=C[state][b]
                assert state in [0,1,2,3,5]
                q=[rows[(t+P)%T][-1]^rows[t][-1] for t in range(T)]
                S=[q[t]|((1-rows[t][-3])&(1-rows[t][-4])) for t in range(T)]
                assert all(rows[(t+P)%T][-2]==1-rows[t][-2] and rows[(t+P)%T][-3]==rows[t][-3] for t in range(T))
                witness.append({'profiles':values,'initial':rows[0],'q':q,'S':S})
            else:
                assert all(rows[(t+P)%T][-1]==rows[t][-1] for t in range(T))
                assert any(rows[(t+P)%T][-2]!=rows[t][-2] for t in range(T))
                witness.append({'profiles':values,'initial':rows[0]})
        if kind=='mode':assert witness[0]['q'][0]!=witness[1]['q'][0] and witness[0]['S']==witness[1]['S']
        out['literal_audit_passed']=True;out['witnesses']=witness
    elif ans==z3.unknown:out['reason_unknown']=s.reason_unknown()
    return out

for args in [('mode',32,16),('mode',64,24),('drop',64,20),('drop',128,24)]:
    out=trial(*args);reports.append(out);print(json.dumps({k:v for k,v in out.items() if k!='witnesses'}),flush=True)
    (r/'boundary-sat-probe.json').write_text(json.dumps({'z3_version':z3.get_version_string(),
       'reports':reports,'Lean_verified':False,'uniform_no_drop_proved':False,
       'uniform_mode_inverse_proved':False,'full_problem_solved':False,
       'seconds':round(time.monotonic()-start,3)},indent=2)+'\n')
