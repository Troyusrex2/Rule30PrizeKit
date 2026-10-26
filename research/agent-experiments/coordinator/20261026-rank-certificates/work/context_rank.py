"""Exact rational version of the same sink-separation rank template.
Every constraint other than a target >=1 is homogeneous. Thus any rational
solution scales to an integer solution by its common positive denominator;
no bounded weight constraints or nonlinear operations are introduced.
Sufficient, exact finite-template search for a sink-separation rank.
Ranks may use local paired context, DFA state and first spatial moments.
UNSAT refutes this potential template, not separation or all possible ranks.
"""
from pathlib import Path
import json,time,sys,os
if os.environ.get('RULE30_Z3_DEPS'):sys.path.insert(0,os.environ['RULE30_Z3_DEPS'])
import z3
root=Path(__file__).resolve().parent
dfa=json.loads((root/'learned-reader.json').read_bytes())['dfa'];reports=[]
selected=(int(sys.argv[1]),bool(int(sys.argv[2]))) if len(sys.argv)==3 else None
output=root/(f'context-rank-{selected[0]}-{int(selected[1])}.json' if selected else 'context-rank.json')
def out(s,p,r):return (((s>>1)^((p>>1)|(r>>1)))<<1)|((s&1)^((p&1)|(r&1)))
for K in ([selected[0]] if selected else [1,2,3,4]):
    begin=time.monotonic();base=4**K
    start=(0,0,0,0,0,0,0);states=[start];index={start:0};edges=[];at=0
    while at<len(states):
        if len(states)>15000:break
        a,b,p,r,ca,cb,np=states[at]
        for s in range(4):
            ns=out(s,p,r)
            target=(dfa['transitions'][a][s],dfa['transitions'][b][ns],s,p,(ca*4+s)%base,(cb*4+ns)%base,ns)
            if target not in index:index[target]=len(states);states.append(target)
            # Feature: state before symbol, K previous paired symbols, new symbol.
            edges.append((at,index[target],(a,ca,s),(b,cb,ns)))
        at+=1
    if at<len(states):
        reports.append({'context':K,'status':'graph_node_cap','states':len(states)});break
    targets={i for i,(a,b,p,r,ca,cb,np) in enumerate(states) if a==15 and p in [0,3] and np in [0,3]}
    # Retain only nodes which can reach a target.
    rev=[[] for _ in states]
    for s,t,_,_ in edges:rev[t].append(s)
    relevant=set(targets);stack=list(targets)
    while stack:
        for p in rev[stack.pop()]:
            if p not in relevant:relevant.add(p);stack.append(p)
    edges=[e for e in edges if e[0] in relevant and e[1] in relevant]
    features=sorted({f for _,_,a,b in edges for f in (a,b)})
    for moment in ([selected[1]] if selected else [False,True]):
        solver=z3.Solver();solver.set(timeout=15000,max_memory=1024)
        V={f:z3.Real('v_'+str(j)) for j,f in enumerate(features)}
        W={f:z3.Real('w_'+str(j)) if moment else z3.RealVal(0) for j,f in enumerate(features)}
        A={i:z3.Real('a_'+str(i)) if moment else z3.RealVal(0) for i in relevant}
        B={i:z3.Real('b_'+str(i)) for i in relevant}
        solver.add(B[0]==0)
        for s,t,a,b in edges:
            solver.add(W[a]-W[b]+A[s]-A[t]>=0)
            solver.add(V[a]-V[b]+B[s]-A[t]-B[t]>=0)
        for i in targets:solver.add(A[i]>=0,B[i]>=1)
        btime=time.monotonic();status=str(solver.check())
        rec={'context':K,'first_moment':moment,'states':len(states),'relevant':len(relevant),
             'edges':len(edges),'features':len(features),'status':status,'seconds':round(time.monotonic()-btime,3)}
        if status=='unknown':rec['reason']=solver.reason_unknown()
        if status=='sat':
            m=solver.model()
            cert={'features':[[*f,str(m.eval(V[f],model_completion=True)),str(m.eval(W[f],model_completion=True))] for f in features],
                  'potentials':[[i,str(m.eval(A[i],model_completion=True)),str(m.eval(B[i],model_completion=True))] for i in relevant]}
            name=f'context-rank-{K}-{int(moment)}-candidate.json'
            (root/name).write_text(json.dumps(cert,indent=2)+'\n',encoding='utf-8');rec['candidate_file']=name
        reports.append(rec);print(json.dumps(rec),flush=True)
        output.write_text(json.dumps({'reports':reports,'Lean_verified':False,
            'sink_separation_proved':False,'full_problem_solved':False},indent=2)+'\n',encoding='utf-8')
        if status=='sat':break
    if reports[-1]['status']=='sat':break
