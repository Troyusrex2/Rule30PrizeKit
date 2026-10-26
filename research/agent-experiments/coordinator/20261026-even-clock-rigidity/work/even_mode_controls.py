"""Independent finite controls for the uniform even-clock rigidity proof.

The five-cell cyclic relaxation permits arbitrary older inputs: it does not
assume finite white ancestry. Enumeration is a control, not the Lean proof.
"""
from pathlib import Path
import itertools,json,time

root=Path(__file__).resolve().parent
start=time.monotonic()
states=list(itertools.product(range(2),repeat=5))

def rule(x,y,z):
    return (30>>(4*x+2*y+z))&1

def transitions(mode):
    allowed=[s for s in states if (s[0] or (not s[2] and not s[3]))
             if mode] if mode else [s for s in states if s[0] or s[1]]
    edges={}
    for a in allowed:
        edges[a]=[b for b in allowed if
            b[0]==(a[0]^(1-a[2]) if mode else rule(*a[:3])) and
            b[1]==rule(*a[1:4]) and b[2]==rule(*a[2:5])]
    return edges

def census(P,mode):
    edges=transitions(mode);closed=qualifying=0;first=None
    # Clock P=1 is deliberately included: the even hypothesis is essential.
    def visit(path):
        nonlocal closed,qualifying,first
        if len(path)==2*P:
            if path[0] not in edges[path[-1]]:return
            closed+=1
            fixed=0 if mode else 2
            if all(path[t+P][fixed]==path[t][fixed] and
                   path[t+P][1]==1-path[t][1] for t in range(P)):
                qualifying+=1
                if first is None:first=path.copy()
            return
        for nxt in edges[path[-1]]:
            t=len(path)
            if t>=P:
                old=path[t-P];fixed=0 if mode else 2
                if nxt[fixed]!=old[fixed] or nxt[1]!=1-old[1]:continue
            visit(path+[nxt])
    for s in edges:visit([s])
    if P%2==0:assert qualifying==0
    else:assert qualifying>0
    return {'clock':P,'relaxation':'mode' if mode else 'saturated_OR',
            'closed_walks_after_half_constraints':closed,
            'qualifying_walks':qualifying,'first_positive_control':first}

reports=[census(P,mode) for mode in [True,False] for P in [1,2,3,4]]
# Truth-table version of the decisive support lemma, with independent Rule 30
# lookup for k's update. Remove either observation and the implication fails.
tested=0;one_observation_controls={0:None,1:None}
for q,k,l,m,n in states:
    a=q or (not k and not l)
    b=(q^(1-k)) or (not rule(k,l,m) and not n)
    if a and b:
        assert (k or l)==k;tested+=1
    if (k or l)!=k:
        for i,ob in enumerate([a,b]):
            if ob and one_observation_controls[i] is None:
                one_observation_controls[i]=[q,k,l,m,n]
assert all(v is not None for v in one_observation_controls.values())
out={'passed':True,'method':'literal rule-30 lookup and exhaustive five-cell cyclic relaxation',
     'support_gate_satisfying_rows':tested,'single_observation_counterexamples':one_observation_controls,
     'reports':reports,'uniform_claim_from_Lean_not_enumeration':True,
     'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
(root/'even-mode-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
