from pathlib import Path
import json
r=Path(__file__).resolve().parent
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa'];T=reader['transitions'];A=set(reader['accepting'])
def update(s,p,q):return (((s>>1)^((p>>1)|(q>>1)))<<1)|((s&1)^((p&1)|(q&1)))
def advance(st,s):
    qr,p,q,u,v,w=st;ns=update(s,p,q);nn=update(ns,u,v)
    return T[qr][s],s,p,ns,u,nn
states=[(0,0,0,0,0,0)];index={states[0]:0};edges=[];bad=None
for st in states:
    row=[]
    for s in range(4):
        nxt=advance(st,s)
        if st[0] in A and all(x in [0,3] for x in [nxt[1],nxt[3],nxt[5]]) and nxt[0] not in A:
            bad={'state':st,'symbol':s,'next':nxt}
        if nxt not in index:index[nxt]=len(states);states.append(nxt)
        row.append(index[nxt])
    edges.append(row)
    assert len(states)<2000
out={'passed':bad is None,'states':states,'edges':edges,'counterexample':bad,
     'Lean_verified':False,'canonical_observer_proved':False,'full_problem_solved':False}
(r/'extension-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':bad is None,'states':len(states),'counterexample':bad}),flush=True)
