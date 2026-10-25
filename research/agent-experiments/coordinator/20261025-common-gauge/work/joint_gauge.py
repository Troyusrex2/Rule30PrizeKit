"""Finite common-gauge constraints; sparse equality contraction only.

Actual differences satisfy both gauges and the wedge constraint. An arbitrary
mode of just one frozen linear evolution need not. No unbounded claim is made.
"""
from pathlib import Path
import json, sys, time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root.parent/'source-renewal-20261025T1840'))
from observer_core import advance, observer
tick=time.monotonic()

def solve(U,V,N,joint):
    origin=U+N+4;mask=(1<<(2*origin+1))-1;a=b=1<<origin
    for _ in range(U):a=advance(a,30)&mask
    for _ in range(V):b=advance(b,30)&mask
    ids={};coords=[];actual=[];equations=[];kinds=[]
    def var(t,p,delta):
        if not -U-t<=p<=U+t:return None
        key=t,p
        if key not in ids:
            ids[key]=len(coords);coords.append(key)
            actual.append((delta>>(origin+p))&1)
        return ids[key]
    def add(terms,kind):
        row=set()
        for x in terms:
            if x is not None:
                if x in row:row.remove(x)
                else:row.add(x)
        if row:
            equations.append(row);kinds.append(kind)
    controls=0
    for t in range(N+1):
        delta=a^b;radius=N-t
        if abs(0)<=radius:add([var(t,0,delta)],'observation')
        if t==N:break
        an,bn=advance(a,30)&mask,advance(b,30)&mask
        for p in range(-radius+1,radius):
            c=(b>>(origin+p+1))&1;r=(a>>(origin+p))&1
            terms=[var(t+1,p,an^bn),var(t,p-1,delta)]
            if not c:terms.append(var(t,p,delta))
            if not r:terms.append(var(t,p+1,delta))
            assert sum(actual[x] for x in terms if x is not None)%2==0
            controls+=1;add(terms,'dynamics')
            if joint:
                terms=[]
                if (delta>>(origin+p+1))&1:terms.append(var(t,p,delta))
                if (delta>>(origin+p))&1:terms.append(var(t,p+1,delta))
                assert sum(actual[x] for x in terms if x is not None)%2==0
                controls+=1;add(terms,'wedge')
        a,b=an,bn
    target=ids[(0,-U)];zero=len(coords);parent=list(range(zero+1));size=[1]*(zero+1)
    def find(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]];x=parent[x]
        return x
    def union(x,y):
        x,y=find(x),find(y)
        if x==y:return False
        if size[x]<size[y]:x,y=y,x
        parent[y]=x;size[x]+=size[y];return True
    rounds=0;merges={k:0 for k in set(kinds)}
    while True:
        changed=False;rounds+=1
        for row,kind in zip(equations,kinds):
            reduced=set();z=find(zero)
            for x in row:
                x=find(x)
                if x==z:continue
                if x in reduced:reduced.remove(x)
                else:reduced.add(x)
            if len(reduced)==1:
                done=union(next(iter(reduced)),zero)
            elif len(reduced)==2:
                x,y=reduced;done=union(x,y)
            else:done=False
            if done:changed=True;merges[kind]+=1
        if not changed:break
    return {'U':U,'V':V,'through':N,'joint_gauges':joint,
        'variables':len(coords),'equations':len(equations),'rounds':rounds,
        'merges_by_kind':merges,'identity_controls':controls,
        'edge_forced':find(target)==find(zero),
        'edge_component_size':size[find(target)],
        'zero_component_size':size[find(zero)]}

records=[];stops=[]
for joint in [False,True]:
    for U in range(1,25):
        failed=False
        for V in range(U):
            if time.monotonic()-tick>210:
                stops.append({'joint':joint,'reason':'internal_time_budget'});failed=True;break
            r=solve(U,V,4*U+32,joint)
            if not r['edge_forced']:
                dense=observer(U,V,30,4*U+32)
                r['single_gauge_dense_certificate']=dense['certificate']
                stops.append({'joint':joint,'reason':'sparse_contraction_insufficient','U':U,'V':V})
                failed=True
            records.append(r)
            if failed:break
        if failed:break
    print(json.dumps({'joint_gauges':joint,'records':sum(r['joint_gauges']==joint for r in records),'last':records[-1]}),flush=True)
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'records':records,'stops':stops,'seconds':time.monotonic()-tick,
     'scope':'Common-gauge field constraints are stronger than one auxiliary evolution. Actual pair differences satisfy them. Sparse contraction failures refute only this finite proof method.'}
(root/'joint-gauge.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'seconds':out['seconds'],'records':len(records),'stops':stops}),flush=True)
