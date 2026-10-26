"""Exact all-word relational laws for the sound two-track reader."""
from pathlib import Path
from collections import deque
import json
r=Path(__file__).resolve().parent
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa']
T=reader['transitions'];A=set(reader['accepting'])
def search(initial,step,bad,alphabet):
    todo=deque([initial]);parent={initial:None};found=None
    while todo:
        q=todo.popleft()
        if bad(q):found=q;break
        for a in alphabet:
            nxt=step(q,a)
            if nxt not in parent:parent[nxt]=(q,a);todo.append(nxt)
    word=None
    if found is not None:
        word=[];q=found
        while parent[q] is not None:q,a=parent[q];word.append(a)
        word.reverse()
    return {'reachable_states':len(parent),'counterexample':word,'passed':found is None,
            'states':list(parent) if found is None else None}
reflexive=search(0,lambda q,a:T[q][3*a],lambda q:q not in A,range(2))
symmetric=search((0,0),lambda q,a:(T[q[0]][a],T[q[1]][((a&1)<<1)|(a>>1)]),
                 lambda q:(q[0] in A)!=(q[1] in A),range(4))
def triple(q,a):
    x,y,z=a>>2,(a>>1)&1,a&1
    return T[q[0]][2*x+y],T[q[1]][2*y+z],T[q[2]][2*x+z]
transitive=search((0,0,0),triple,lambda q:q[0] in A and q[1] in A and q[2] not in A,range(8))
out={'reflexive':reflexive,'symmetric':symmetric,'transitive':transitive,'Lean_verified':False,
     'full_problem_solved':False}
if transitive['counterexample'] is not None:
    w=transitive['counterexample'];out['initial_triple']=[[((s>>bit)&1) for s in w] for bit in [2,1,0]]
(r/'reader-equivalence-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:({a:b for a,b in v.items() if a!='states'} if isinstance(v,dict) else v) for k,v in out.items()}))
