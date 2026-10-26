"""Check the proposed finite normal forms against the reader, for all words."""
from pathlib import Path
from collections import deque
import json
r=Path(__file__).resolve().parent
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa'];T=reader['transitions'];A=set(reader['accepting'])
C=[[0,1],[2,3],[4,6],[6,4],[5,5],[5,5],[6,6]];CA={0,1,2,3,5}
def bfs(initial,alphabet,step,bad,cap=5000):
    states=[initial];index={initial:0};parents=[None];edges=[];at=0;failure=None
    while at<len(states):
        if bad(states[at]):failure=at;break
        row=[]
        for a in alphabet:
            v=step(states[at],a)
            if v not in index:index[v]=len(states);states.append(v);parents.append((at,a))
            row.append(index[v])
        edges.append(row);at+=1
        if len(states)>cap:break
    word=None
    if failure is not None:
        word=[];j=failure
        while parents[j] is not None:j,a=parents[j];word.append(a)
        word.reverse()
    return {'states':states,'edges':edges,'complete':at==len(states),'counterexample':word,'processed':at}
def cover_step(S,x):return tuple(sorted({(T[q][2*x+y],C[c][y]) for q,c in S for y in range(2)}))
coverage=bfs(((0,0),),range(2),cover_step,lambda S:not any(q in A and c in CA for q,c in S))
def unique_step(s,a):
    q,c,d,diff=s;x,y=a>>1,a&1
    return T[q][a],C[c][x],C[d][y],diff or x!=y
unique=bfs((0,0,0,False),range(4),unique_step,
           lambda s:s[0] in A and s[1] in CA and s[2] in CA and s[3])
def time_step(s,x):
    c,d,p,q=s;y=x^(p|q)
    return C[c][x],C[d][y],x,p
stable=bfs((0,0,0,0),range(2),time_step,lambda s:(s[0] in CA)!=(s[1] in CA))
counts=[int(q in CA) for q in range(7)];count_reports=[]
for n in range(33):
    if n>=3:assert counts[0]==1<<(n-1)
    count_reports.append({'width':n,'canonical_words':counts[0]})
    counts=[sum(counts[C[q][x]] for x in range(2)) for q in range(7)]
out={'canonical_transitions':C,'canonical_accepting':sorted(CA),
     'coverage':coverage,'unique':unique,'time_invariance':stable,'counts':count_reports,
     'Lean_verified':False,'full_problem_solved':False}
(r/'canonical-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:{'states':len(v['states']),'complete':v['complete'],'counterexample':v['counterexample']}
                  for k,v in [('coverage',coverage),('unique',unique),('time_invariance',stable)]}))
