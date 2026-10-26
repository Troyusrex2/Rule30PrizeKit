"""Try an additive automaton ranking proving completeness of the learned DFA.
UNSAT only rules out this ranking template.
"""
from pathlib import Path
import json,sys
sys.path.insert(0,r'D:\MWB\Rule30\wolfram-local\z3-deps')
import z3
ROOT=Path(__file__).resolve().parent
dfa=json.loads((ROOT/'learned-reader.json').read_bytes())['dfa']
prod=json.loads((ROOT/'invariance-product.json').read_bytes());states=prod['states'];edges=prod['edges']
def output(sym,p,q):return (((sym>>1)^((p>>1)|(q>>1)))<<1)|((sym&1)^((p&1)|(q&1)))
reports=[]
for template in ['state','edge']:
    solver=z3.Solver();solver.set(timeout=10000,max_memory=1024)
    w=[[z3.Int(f'w_{i}_{j}') for j in range(1 if template=='state' else 4)] for i in range(17)]
    v=[z3.Int('p_'+str(i)) for i in range(len(states))]
    for row in w:
        for x in row:solver.add(x>=0)
    solver.add(v[0]==0)
    for i,(a,b,p,q) in enumerate(states):
        if a not in dfa['accepting'] and p in [0,3]:solver.add(v[i]>=1)
        for sym,j in enumerate(edges[i]):
            out=output(sym,p,q)
            if template=='state':
                delta=w[dfa['transitions'][a][sym]][0]-w[dfa['transitions'][b][out]][0]
            else:delta=w[a][sym]-w[b][out]
            solver.add(delta>=v[j]-v[i])
    status=solver.check();r={'template':template,'status':str(status)}
    if status==z3.sat:
        model=solver.model();r['weights']=[[model.eval(x).as_long() for x in row] for row in w]
        r['potentials']=[model.eval(x).as_long() for x in v]
        for i,(a,b,p,q) in enumerate(states):
            for sym,j in enumerate(edges[i]):
                out=output(sym,p,q)
                diff=(r['weights'][dfa['transitions'][a][sym]][0]-r['weights'][dfa['transitions'][b][out]][0]) if template=='state' else (r['weights'][a][sym]-r['weights'][b][out])
                assert diff>=r['potentials'][j]-r['potentials'][i]
    elif status==z3.unknown:r['reason_unknown']=solver.reason_unknown()
    reports.append(r);print(json.dumps(r),flush=True)
(ROOT/'rank-synthesis.json').write_text(json.dumps({'reports':reports,'Lean_verified':False,'completeness_proved':False},indent=2)+'\n',encoding='utf-8')
