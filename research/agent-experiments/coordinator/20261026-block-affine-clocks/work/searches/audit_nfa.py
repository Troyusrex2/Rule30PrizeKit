"""Independent semantic and CNF control; no invariant or completeness claim."""
from pathlib import Path
from functools import lru_cache
import json,itertools,time
r=Path(__file__).resolve().parent
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa']
def convert(w,c):
    x,y=c>>1,c&1;out=[]
    for a in w:
        u,v,up,vp=a>>3,(a>>2)&1,(a>>1)&1,a&1
        out.append((v<<3)|(x<<2)|(vp<<1)|y)
        x=(30>>((x<<2)|(u<<1)|v))&1;y=(30>>((y<<2)|(up<<1)|vp))&1
    return tuple(out),(x<<1)|y
def safe(q,w):return q!=15 or any(((a>>2)&1)!=(a&1) for a in w)
def negative(q,w):
    if not safe(q,w):return True
    return any(last==c and not safe(reader['transitions'][q][c],out)
               for c in range(4) for out,last in [convert(w,c)])
graph={}
for P in [2,4,8,16]:
    src=r/f'clock-product-{P}-graph.json'
    data=src.read_bytes()
    graph[P]={tuple(x) for x in json.loads(data)['states']}
def positive(q,w):
    if q==0 and not any(w):return True
    vs=[sum(((a>>bit)&1)<<t for t,a in enumerate(w)) for bit in [3,2,1,0]]
    return (*vs,q) in graph.get(len(w),set())
reports=[]
for name,reverse in [('nfa-samples.json',False),('reverse-nfa-samples.json',True),('hinted-reverse-nfa-samples.json',True)]:
    if not (r/name).exists():continue
    data=json.loads((r/name).read_bytes())
    def w(x):return tuple(reversed(x)) if reverse else tuple(x)
    assert all(positive(q,w(x)) for q,x in data['positive'])
    assert all(negative(q,w(x)) for q,x in data['negative'])
    assert all(any(reader['transitions'][q][c]==qp and convert(w(x),c)==(w(y),c) for c in range(4))
               for q,x,qp,y in data['implications'])
    reports.append({'file':name,'positive':len(data['positive']),'negative':len(data['negative']),
                    'implications':len(data['implications']),'passed':True})
# Load definitions only. No search main loop is executed by this import.
source=(r/'learn_hinted_reverse_nfa.py').read_text(encoding='utf-8')
ns={'__file__':str(r/'learn_hinted_reverse_nfa.py')};exec(source.split('history=[];K=9;')[0],ns)
reverse_controls=0
for size in [1,2,3]:
    for w in itertools.product(range(16),repeat=size):
        for c in range(4):
            out,last=convert(w,c)
            rev,start=ns['transform'](tuple(reversed(w)),last)
            assert rev==tuple(reversed(out)) and start==c;reverse_controls+=1
old=json.loads((r/'prior-word-candidate.json').read_bytes());K=len(old['delta'])//2
m={'start':sum(1<<i for i in range(K) if old['accepting'][2*i+1]),
   'delta':[[sum(1<<i for i in range(K) if old['delta'][2*i][a]//2==j) for j in range(K)] for a in range(16)],
   'accept':[1<<(s//2) for s in old['starts']]}
step,raw=ns['machine'](m)
# This is an encoding control on facts satisfied by a known finite model.
# The actual learner retains every fact; no actual experiment is rerun here.
orig=(len(ns['positive']),len(ns['negative']),len(ns['implications']))
ns['positive']={x for x in ns['positive'] if raw(*x)}
ns['negative']={x for x in ns['negative'] if not raw(*x)}
ns['implications']={x for x in ns['implications'] if not raw(x[0],x[1]) or raw(x[2],x[3])}
kept=(len(ns['positive']),len(ns['negative']),len(ns['implications']))
BaseSolver=ns['Minisat22']
class ForcedHintSolver(BaseSolver):
    def set_phases(self,phases):
        self.append_formula([[p] for p in phases])
ns['Minisat22']=ForcedHintSolver
known,meta=ns['learn'](K);assert known is not None,meta
assert meta['status']=='sat'
assert all(bool(raw(q,w))==bool(ns['machine'](known)[1](q,w)) for q,w in ns['positive']|ns['negative'])
out={'passed':True,'sample_audits':reports,'reverse_carry_controls':reverse_controls,
     'forced_known_model_encoding_passed':True,'known_model_states':K,
     'encoding_control_original_fact_counts':orig,'encoding_control_kept_fact_counts':kept,
     'encoding_control_solver':meta,'actual_search_constraints_removed':False,
     'Lean_verified':False,'full_problem_solved':False}
(r/'nfa-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out),flush=True)
