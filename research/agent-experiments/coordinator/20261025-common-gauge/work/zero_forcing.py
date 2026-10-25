"""Does sparse zero forcing suffice for the finite canonical observer?

This is structural peeling of exact homogeneous equations, rather than
dense Gaussian elimination. Failure only refutes this weaker proof method.
"""
from pathlib import Path
from collections import deque
import json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root.parent/'source-renewal-20261025T1840'))
from observer_core import observer,advance
tick=time.monotonic();records=[]
def force(U,V,N,rule=30):
    origin=U+N+4;mask=(1<<(2*origin+1))-1;a=b=1<<origin
    for _ in range(U):a=advance(a,rule)&mask
    for _ in range(V):b=advance(b,rule)&mask
    ids={};variables=[];equations=[];adjacency=[]
    def var(t,p):
        if p==0 or p < -U-t or p > U+t:return None
        key=(t,p)
        if key not in ids:
            ids[key]=len(variables);variables.append(key);adjacency.append([])
        return ids[key]
    for t in range(N):
        radius=N-t-1
        for p in range(-radius,radius+1):
            cc=((b>>(origin+p+1))&1)^(1 if rule==30 else 0)
            rc=1^((a>>(origin+p))&1)
            terms=[var(t+1,p),var(t,p-1)]
            if cc:terms.append(var(t,p))
            if rc:terms.append(var(t,p+1))
            row=set(x for x in terms if x is not None)
            if row:
                j=len(equations);equations.append(row)
                for x in row:adjacency[x].append(j)
        a,b=advance(a,rule)&mask,advance(b,rule)&mask
    target=ids[(0,-U)];queue=deque(j for j,row in enumerate(equations) if len(row)==1)
    forced=set();reasons=[]
    while queue:
        j=queue.popleft();row=equations[j]
        if len(row)!=1:continue
        x=next(iter(row))
        if x in forced:continue
        forced.add(x);reasons.append((x,j))
        for k in adjacency[x]:
            equations[k].discard(x)
            if len(equations[k])==1:queue.append(k)
    return {'U':U,'V':V,'rule':rule,'through':N,'variables':len(variables),
            'equations':len(equations),'forced_variables':len(forced),
            'edge_forced':target in forced,'left_unknown':sum(1 for i,(t,p) in enumerate(variables) if i not in forced and p<0),
            'remaining_sizes':{str(k):sum(len(r)==k for r in equations) for k in range(5)}}
pairs=[(u,v) for u in range(1,17) for v in range(u)]
stop=None
for U,V in pairs:
    if time.monotonic()-tick>210:stop='internal_time_budget';break
    r=force(U,V,4*U+32)
    if not r['edge_forced']:
        dense=observer(U,V,30,4*U+32)
        r['dense_certificate']=dense['certificate'];r['dense_unresolved']=dense['unresolved']
        records.append(r);stop='sparse_peeling_insufficient';print(json.dumps(r),flush=True);break
    records.append(r)
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'records':records,'stop':stop,'seconds':time.monotonic()-tick,
     'scope':'Exact finite-cone sparse zero forcing. A failure is not an observer or prize counterexample; it shows that genuine linear combinations beyond degree-one peeling are needed.'}
(root/'zero-forcing.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'tested':len(records),'stop':stop,'seconds':out['seconds']}),flush=True)
