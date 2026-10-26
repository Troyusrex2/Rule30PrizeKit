"""Inspect representative tables for recorded finite training corpora.
Recovered tables are not claimed identical to prior solver models.
"""
from pathlib import Path
import ast,json,time,sys
import numpy as np
r=Path(__file__).resolve().parent;sys.path.insert(0,str(r/'solver-deps'))
import z3
from profile_data import graph,literal
start=time.monotonic();results=[]
for kind,S,n in [('tree',6,74),('zip',10,62)]:
    filename='tree_reader_probe.py' if kind=='tree' else 'zip_reader_probe.py'
    meta=json.loads((r/(kind+'-reader-probe.json')).read_bytes())
    parsed=ast.parse((r/filename).read_text(encoding='utf-8'))
    fn=next(x for x in parsed.body if isinstance(x,ast.FunctionDef) and x.name=='synthesize')
    # A separate, explicit 30-second budget for reconstructing a known-SAT
    # training corpus; original experiment statuses and guards stay unchanged.
    class Timeout(ast.NodeTransformer):
        def visit_keyword(self,node):
            if node.arg=='timeout':node.value=ast.Constant(value=30000)
            return node
    fn=Timeout().visit(fn)
    module=ast.Module(body=[fn],type_ignores=[]);ast.fix_missing_locations(module)
    context={'z3':z3,'np':np,'time':time,'train':meta['training_samples'][:n]}
    exec(compile(module,filename,'exec'),context)
    answer=context['synthesize'](S,4) if kind=='tree' else context['synthesize'](S)
    if kind=='tree':rec,table,outputs=answer
    else:
        status,seconds,nodes,table,outputs=answer;rec={'status':status,'solver_seconds':seconds,'prefix_nodes':nodes}
    assert table is not None,rec
    data,_=graph(32)
    if kind=='zip':data=[d for d in data if d['OR_profile']&((1<<16)-1)!=d['OR_profile']>>16]
    groups={};wrong=0
    for d in data:
        P=d['clock'];w=d['OR_profile']
        if kind=='tree':
            states=[(w>>i)&1 for i in range(P)]
            while len(states)>1:states=[int(table[states[i],states[i+1]]) for i in range(0,len(states),2)]
            state=states[0]
        else:
            state=0
            for t in range(P//2):state=int(table[state,((w>>t)&1)+2*((w>>(t+P//2))&1)])
        if int(outputs[state])!=d['target']:wrong+=1
        groups.setdefault(state,{})[d['target']]=d
    conflicts=[]
    for state,pair in groups.items():
        if len(pair)==2:
            a,b=pair[0],pair[1];literal(a);literal(b)
            conflicts.append({'learned_state':state,'target_zero':a,'target_one':b})
    assert conflicts and wrong
    results.append({'kind':kind,'states':S,'training_rows':n,'reconstructed_status':rec,
     'transition_table':table.tolist(),'outputs':outputs.tolist(),'validation_clock':32,
     'validation_profiles':len(data),'wrong_predictions':wrong,'mixed_target_state_witnesses':conflicts,
     'recovered_table_not_claimed_identical_to_original':True,'inspection_solver_timeout_ms':30000,
     'interpretation':'The learned transition table merges valid profiles with opposite targets; no output relabeling repairs it.'})
out={'passed':True,'readers':results,'candidate_uniform_decoder_found':False,'Lean_verified':False,
 'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
(r/'learned-reader-inspection.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'readers':[{'kind':x['kind'],'states':x['states'],'wrong_predictions':x['wrong_predictions'],
 'mixed_target_states':len(x['mixed_target_state_witnesses'])} for x in results],'seconds':out['seconds']}))
