"""Learn a temporal decoder reading aligned halves at the least OR clock.
This is a bounded CEGIS experiment, not a uniform observer theorem.
"""
from pathlib import Path
import sys,json,time,random
import numpy as np
from numba import njit
r=Path(__file__).resolve().parent;sys.path.insert(0,str(r/'solver-deps'))
import z3
from profile_data import graph,literal,C
START=time.monotonic();train=[];seen=set();datasets={};reports=[];candidate=None;controls=0

def least_period(P,w):
    while P>1 and (w&((1<<(P//2))-1))==(w>>(P//2)):P//=2;w&=(1<<P)-1
    return P

def audit(d):
    global controls
    literal(d);q=0
    for b in d['parent_initial']+[0]:q=C[q][b]
    assert q in {0,1,2,3,5};assert least_period(d['clock'],d['OR_profile'])==d['clock']
    controls+=1

def get_data(P):
    if P not in datasets:
        raw,states=graph(P);data=[d for d in raw if least_period(P,d['OR_profile'])==P]
        arrays=(np.array([d['OR_profile'] for d in data],dtype=np.uint64),
                np.array([d['target'] for d in data],dtype=np.int8))
        datasets[P]=(data,arrays,states)
    return datasets[P]

for P in [2,4,8]:
    data,_,_=get_data(P)
    for d in data:train.append(d);seen.add((P,d['OR_profile']));audit(d)

@njit(cache=False)
def wrong_rows(P,profiles,targets,table,outputs):
    bad=np.empty(len(profiles),np.int32);count=0
    for row in range(len(profiles)):
        state=0
        for t in range(P//2):
            symbol=int((profiles[row]>>t)&np.uint64(1))+2*int((profiles[row]>>(t+P//2))&np.uint64(1))
            state=table[state,symbol]
        if outputs[state]!=targets[row]:bad[count]=row;count+=1
    return bad[:count]

def synthesize(S):
    solver=z3.Solver();solver.set(timeout=6000,random_seed=9472,max_memory=1536)
    F=z3.Function('F',z3.IntSort(),z3.IntSort(),z3.IntSort());O=z3.Function('O',z3.IntSort(),z3.BoolSort())
    for a in range(S):
        for b in range(4):solver.add(F(a,b)>=0,F(a,b)<S)
    nodes={():z3.IntVal(0)}
    for d in train:
        P=d['clock'];w=d['OR_profile'];prefix=()
        for t in range(P//2):
            symbol=((w>>t)&1)+2*((w>>(t+P//2))&1);nxt=prefix+(symbol,)
            if nxt not in nodes:
                v=z3.Int('q'+str(len(nodes)));solver.add(v==F(nodes[prefix],symbol),v>=0,v<S);nodes[nxt]=v
            prefix=nxt
        solver.add(O(nodes[prefix])==bool(d['target']))
    t=time.monotonic();status=solver.check();seconds=time.monotonic()-t
    if status!=z3.sat:return str(status),seconds,len(nodes),None,None
    m=solver.model();table=np.array([[m.eval(F(a,b),model_completion=True).as_long() for b in range(4)] for a in range(S)],dtype=np.int32)
    outputs=np.array([int(z3.is_true(m.eval(O(a),model_completion=True))) for a in range(S)],dtype=np.int8)
    return str(status),seconds,len(nodes),table,outputs

for S in [2,3,4,5,6,8,10,12,16]:
    for iteration in range(24):
        if time.monotonic()-START>180:break
        status,seconds,nodes,table,outputs=synthesize(S)
        rec={'states':S,'iteration':iteration,'status':status,'training_rows':len(train),
             'prefix_nodes':nodes,'solver_seconds':round(seconds,3)}
        if table is None:reports.append(rec);print(json.dumps(rec),flush=True);break
        added=0;validation=[]
        for P in [2,4,8,16,32,64]:
            data,arrays,count=get_data(P);bad=wrong_rows(P,*arrays,table,outputs)
            validation.append({'clock':P,'least_clock_profiles':len(data),'wrong':len(bad)})
            if len(bad):
                picks=list(map(int,bad[:12]))
                if len(bad)>12:picks+=random.Random(S*100+iteration).sample(list(map(int,bad[12:])),min(12,len(bad)-12))
                for i in picks:
                    d=data[i];key=(P,d['OR_profile'])
                    if key not in seen:audit(d);train.append(d);seen.add(key);added+=1
                assert added>0;break
        rec['validation']=validation;rec['counterexamples_added']=added
        reports.append(rec);print(json.dumps(rec),flush=True)
        if not added:
            candidate={'states':S,'table':table.tolist(),'outputs':outputs.tolist(),
                       'least_clocks_validated':[2,4,8,16,32,64],'uniform_correctness_proved':False}
            break
    if candidate or time.monotonic()-START>180:break
out={'reports':reports,'candidate':candidate,'training_samples':train,'literal_canonical_controls':controls,
     'least_OR_clock_required':True,'finite_clocks_only':True,'Lean_verified':False,
     'canonical_observer_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-START,3)}
(r/'zip-reader-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['reports','training_samples']}),flush=True)
