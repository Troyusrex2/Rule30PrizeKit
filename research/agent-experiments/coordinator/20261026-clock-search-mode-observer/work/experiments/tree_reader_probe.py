"""CEGIS for a finite algebra on dyadic halves; finite data, no uniform proof."""
from pathlib import Path
import json,time,random,sys
r=Path(__file__).resolve().parent
sys.path.insert(0,str(r/'solver-deps'))
import numpy as np
from numba import njit
import z3
from profile_data import graph,literal,C
r=Path(__file__).resolve().parent;START=time.monotonic();TOTAL_SECONDS=180
train=json.loads((r/'small-profile-samples.json').read_bytes())
ones,_=graph(1);train=ones+train;seen={(d['clock'],d['OR_profile']) for d in train}
datasets={};reports=[];found=None;literal_controls=0

def audit(d):
    global literal_controls
    literal(d);q=0
    for b in d['parent_initial']+[0]:q=C[q][b]
    assert q in {0,1,2,3,5}
    literal_controls+=1

for d in train:audit(d)

@njit(cache=False)
def wrong_rows(profiles,clocks,targets,table,outputs):
    bad=np.empty(len(profiles),np.int32);count=0;values=np.empty(64,np.int32)
    for row in range(len(profiles)):
        size=clocks[row]
        for i in range(size):values[i]=int((profiles[row]>>i)&np.uint64(1))
        while size>1:
            size//=2
            for i in range(size):values[i]=table[values[2*i],values[2*i+1]]
        if outputs[values[0]]!=targets[row]:bad[count]=row;count+=1
    return bad[:count]

def get_data(P):
    if P not in datasets:
        data,states=graph(P)
        arrays=(np.array([d['OR_profile'] for d in data],dtype=np.uint64),
                np.array([d['clock'] for d in data],dtype=np.int32),
                np.array([d['target'] for d in data],dtype=np.int8))
        datasets[P]=(data,arrays,states)
    return datasets[P]

def synthesize(S,iteration):
    solver=z3.Solver();solver.set(timeout=5000,random_seed=7241,max_memory=1536)
    F=z3.Function('F',z3.IntSort(),z3.IntSort(),z3.IntSort())
    O=z3.Function('O',z3.IntSort(),z3.BoolSort())
    for a in range(S):
        for b in range(S):solver.add(F(a,b)>=0,F(a,b)<S)
    nodes={}
    def node(P,w):
        key=(P,w)
        if key in nodes:return nodes[key]
        if P==1:v=z3.IntVal(w)
        else:
            half=P//2;lo=node(half,w&((1<<half)-1));hi=node(half,w>>half)
            v=z3.Int('q'+str(len(nodes)));solver.add(v==F(lo,hi),v>=0,v<S)
        nodes[key]=v;return v
    for d in train:solver.add(O(node(d['clock'],d['OR_profile']))==bool(d['target']))
    start=time.monotonic();status=solver.check();elapsed=time.monotonic()-start
    rec={'states':S,'iteration':iteration,'training_rows':len(train),'tree_nodes':len(nodes),
         'status':str(status),'solver_seconds':round(elapsed,3)}
    if status!=z3.sat:return rec,None,None
    model=solver.model()
    table=np.array([[model.eval(F(a,b),model_completion=True).as_long() for b in range(S)] for a in range(S)],dtype=np.int32)
    outputs=np.array([int(z3.is_true(model.eval(O(a),model_completion=True))) for a in range(S)],dtype=np.int8)
    return rec,table,outputs

for S in [2,3,4,5,6,8,10,12]:
    for iteration in range(20):
        if time.monotonic()-START>TOTAL_SECONDS:break
        rec,table,outputs=synthesize(S,iteration)
        if table is None:reports.append(rec);print(json.dumps(rec),flush=True);break
        added=0;validation=[]
        for P in [1,2,4,8,16,32,64]:
            data,arrays,count=get_data(P);bad=wrong_rows(*arrays,table,outputs)
            validation.append({'clock':P,'product_states':count,'valid_profiles':len(data),'wrong':len(bad)})
            if len(bad):
                picks=list(map(int,bad[:12]))
                if len(bad)>12:picks+=random.Random(S*100+iteration).sample(list(map(int,bad[12:])),min(12,len(bad)-12))
                for i in picks:
                    d=data[i];key=(P,d['OR_profile'])
                    if key not in seen:audit(d);train.append(d);seen.add(key);added+=1
                assert added>0
                break
        rec['validation']=validation;rec['counterexamples_added']=added
        reports.append(rec);print(json.dumps(rec),flush=True)
        if not added:
            found={'states':S,'table':table.tolist(),'outputs':outputs.tolist(),
                   'validated_clocks':[1,2,4,8,16,32,64],'uniform_correctness_proved':False}
            break
    if found or time.monotonic()-START>TOTAL_SECONDS:break
out={'reports':reports,'candidate':found,'training_rows':len(train),'literal_and_canonical_controls':literal_controls,
     'training_samples':train,'finite_clocks_only':True,'Lean_verified':False,
     'canonical_observer_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-START,3)}
(r/'tree-reader-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['reports','training_samples']}),flush=True)
