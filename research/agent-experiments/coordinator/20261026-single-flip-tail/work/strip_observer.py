"""Exact finite controlled strip; shared tail inputs are not assumed realizable.
Pure periodicity of finite right-bounded states must be retained separately.
"""
from pathlib import Path
from collections import deque
import json,math
root=Path(__file__).resolve().parent
def advance(st,r,s):
    a,b,u,v=st;aa=a|(u<<5)|(v<<6);bb=b|(u<<5)|(v<<6)
    an=(aa^((aa>>1)|(aa>>2)))&31;bn=(bb^((bb>>1)|(bb>>2)))&31
    un=u^(v|r);vn=v^(r|s)
    return an,bn,un,vn
initials=[(10,20,u,v) for u in (0,1) for v in (0,1)]
states=initials.copy();ids={st:i for i,st in enumerate(states)};edges=[];rev=[[] for _ in states];at=0
while at<len(states):
    row=[]
    for r in (0,1):
        for s in (0,1):
            nxt=advance(states[at],r,s)
            if (nxt[0]^nxt[1])&1:continue
            if nxt not in ids:ids[nxt]=len(states);states.append(nxt);rev.append([])
            j=ids[nxt];row.append((j,r,s));rev[j].append(at)
    edges.append(row);at+=1
# Iterative DFS finish order, then reverse components.
seen=set();order=[]
for i in range(len(states)):
    if i in seen:continue
    stack=[(i,False)]
    while stack:
        j,done=stack.pop()
        if done:order.append(j);continue
        if j in seen:continue
        seen.add(j);stack.append((j,True))
        stack.extend((t,False) for t,_,_ in edges[j] if t not in seen)
component={};groups=[]
for i in reversed(order):
    if i in component:continue
    group=[];stack=[i];component[i]=len(groups)
    while stack:
        j=stack.pop();group.append(j)
        for t in rev[j]:
            if t not in component:component[t]=len(groups);stack.append(t)
    groups.append(group)
reports=[]
for c,g in enumerate(groups):
    if not any(i<4 for i in g):continue
    dist={g[0]:0};todo=deque([g[0]])
    while todo:
        i=todo.popleft()
        for j,_,_ in edges[i]:
            if component[j]==c and j not in dist:dist[j]=dist[i]+1;todo.append(j)
    gcd=0
    for i in g:
        for j,_,_ in edges[i]:
            if component[j]==c:gcd=math.gcd(gcd,abs(dist[i]+1-dist[j]))
    branch=[i for i in g if len({j for j,_,_ in edges[i] if component[j]==c})>1]
    rec={'component':c,'states':len(g),'initial_states':[i for i in g if i<4],
         'cycle_length_gcd':gcd,'can_have_power_of_two_cycle_length':gcd>0 and gcd&(gcd-1)==0,
         'branching_states':len(branch)}
    reports.append(rec);print(json.dumps(rec),flush=True)
payload={'states':states,'edges':edges,'components':groups,'reports':reports,
         'Lean_verified':False,'shared_input_realizability_proved':False,
         'reader_completeness_proved':False,'full_problem_solved':False}
(root/'strip-observer.json').write_text(json.dumps(payload,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'total_states':len(states),'components':len(groups),'initial_component_reports':reports}),flush=True)
