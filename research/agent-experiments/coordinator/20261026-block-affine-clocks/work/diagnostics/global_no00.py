"""Fast falsification of a boundary-free dyadic OR=1 rigidity hypothesis.
Finite graph diagnostics only; no all-clock theorem is inferred.
"""
from pathlib import Path
from collections import deque
import json
r=Path(__file__).resolve().parent
def integral(g,b,P):
    x=g;s=1;mask=(1<<P)-1
    while s<P:x^=x<<s;s*=2
    return ((x<<1)&mask)^(mask if b else 0)
reports=[]
for P in [2,4,8]:
    N=1<<P;mask=N-1;total=N*N
    edges=[None]*total;indegree=[0]*total
    for u in range(N):
        for v in range(N):
            g=u|v;i=u*N+v
            if g.bit_count()%2:edges[i]=[];continue
            lo=integral(g,0,P);edges[i]=[v*N+lo,v*N+(lo^mask)]
            for j in edges[i]:indegree[j]+=1
    todo=deque(i for i,d in enumerate(indegree) if d==0);removed=bytearray(total)
    while todo:
        i=todo.popleft();removed[i]=1
        for j in edges[i]:
            indegree[j]-=1
            if indegree[j]==0:todo.append(j)
    def period2(v):return all(((v>>t)&1)==((v>>((t+2)%P))&1) for t in range(P))
    cex=None;no00=0
    for i in range(total):
        if removed[i]:continue
        u,v=divmod(i,N)
        vn=(v>>1)|((v&1)<<(P-1))
        if v|vn==mask and not period2(v):no00+=1
        if u|v==mask and (not period2(u) or not period2(v)):
            cex={'u':u,'v':v};break
    if cex:
        # Recover an explicit eventually cyclic predecessor chain, not merely an indegree count.
        rev={}
        for i,row in enumerate(edges):
            if removed[i]:continue
            for j in row:
                if not removed[j] and j not in rev:rev[j]=i
        path=[];seen={};i=cex['u']*N+cex['v']
        while i not in seen:
            seen[i]=len(path);path.append(list(divmod(i,N)));i=rev[i]
        cex.update(backward_path=path,repeat_from=seen[i])
    rep={'clock':P,'all_profile_pairs':total,'has_infinite_ancestry':total-sum(removed),
         'non_period_two_no00_pairs_seen':no00,'OR_one_counterexample':cex}
    reports.append(rep);print(json.dumps(rep),flush=True)
    if cex:break
(r/'global-no00.json').write_text(json.dumps({'reports':reports,'Lean_verified':False,
 'white_boundary_counterexample':False,'all_clock_rigidity_proved':False,'full_problem_solved':False},indent=2)+'\n',encoding='utf-8')
