"""Allow several physical updates between decreases of an automaton rank."""
from pathlib import Path
import json,sys,time
sys.path.insert(0,r'D:\MWB\Rule30\wolfram-local\z3-deps')
import z3
ROOT=Path(__file__).resolve().parent
dfa=json.loads((ROOT/'learned-reader.json').read_bytes())['dfa']
def output(sym,p,q):return (((sym>>1)^((p>>1)|(q>>1)))<<1)|((sym&1)^((p&1)|(q&1)))
reports=[]
for K in [2,3,4,6]:
    initial=(0,0,*([0,0]*K),0);states=[initial];indices={initial:0};edges=[];at=0;cut=False
    while at<len(states):
        if len(states)>50000:cut=True;break
        s=states[at];a,b=s[:2];memory=s[2:-1];row=[]
        for sym in range(4):
            value=sym;new=[]
            for i in range(K):
                p,q=memory[2*i:2*i+2];new.extend([value,p]);value=output(value,p,q)
            state=(dfa['transitions'][a][sym],dfa['transitions'][b][value],*new,value)
            if state not in indices:indices[state]=len(states);states.append(state)
            row.append((indices[state],value))
        edges.append(row);at+=1
    if cut:
        reports.append({'updates':K,'states':len(states),'status':'graph_node_cap'});break
    solver=z3.Solver();solver.set(timeout=12000,max_memory=1536)
    weights=[[z3.Int(f'w_{i}_{j}') for j in range(4)] for i in range(17)]
    potential=[z3.Int('p_'+str(i)) for i in range(len(states))]
    for row in weights:
        for w in row:solver.add(w>=0)
    solver.add(potential[0]==0)
    targets=0
    for i,s in enumerate(states):
        a,b=s[:2]
        if a not in dfa['accepting'] and all(s[2+2*j] in [0,3] for j in range(K)) and s[-1] in [0,3]:
            solver.add(potential[i]>=1);targets+=1
        for sym,(j,out) in enumerate(edges[i]):solver.add(weights[a][sym]-weights[b][out]>=potential[j]-potential[i])
    begin=time.monotonic();status=solver.check()
    r={'updates':K,'states':len(states),'targets':targets,'status':str(status),'seconds':round(time.monotonic()-begin,3)}
    if status==z3.sat:
        m=solver.model();r['weights']=[[m.eval(w).as_long() for w in row] for row in weights]
        r['potentials']=[m.eval(v).as_long() for v in potential]
    elif status==z3.unknown:r['reason_unknown']=solver.reason_unknown()
    reports.append(r);print(json.dumps(r),flush=True)
    if status==z3.sat:break
(ROOT/'macro-rank.json').write_text(json.dumps({'reports':reports,'Lean_verified':False,'reader_completeness_proved':False},indent=2)+'\n',encoding='utf-8')
