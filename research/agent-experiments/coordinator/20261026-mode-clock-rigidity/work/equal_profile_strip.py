"""Look for a finite local proof that equal adjacent periodic profiles alternate.

Two oldest cells are arbitrary each step. Positive walks in this relaxation
are not certificates of finite white ancestry.
"""
from pathlib import Path
from collections import deque
import json,time
r=Path(__file__).resolve().parent;start=time.monotonic();reports=[]

def analyze(width):
    mask=(1<<width)-1;top=width-1
    nodes=[x for x in range(1<<width) if (x>>top&1)==(x>>(top-1)&1)]
    edges={};rev={x:[] for x in nodes}
    for x in nodes:
        high=(x^((x<<1)|(x<<2)))&mask&~3
        ys=[high|b for b in range(4) if (high>>top&1)==(high>>(top-1)&1)]
        edges[x]=ys
        for y in ys:rev[y].append(x)
    seen=set();order=[]
    for x in nodes:
        if x in seen:continue
        stack=[(x,0)];seen.add(x)
        while stack:
            v,i=stack[-1]
            if i==len(edges[v]):order.append(v);stack.pop();continue
            stack[-1]=(v,i+1);y=edges[v][i]
            if y not in seen:seen.add(y);stack.append((y,0))
    label={};components=[]
    for x in reversed(order):
        if x in label:continue
        idx=len(components);component=[];stack=[x];label[x]=idx
        while stack:
            v=stack.pop();component.append(v)
            for y in rev[v]:
                if y not in label:label[y]=idx;stack.append(y)
        components.append(component)
    witness=None;nontrivial=0
    def path(a,b,idx):
        todo=deque([a]);prev={a:None}
        while todo:
            x=todo.popleft()
            if x==b:
                out=[]
                while x is not None:out.append(x);x=prev[x]
                return out[::-1]
            for y in edges[x]:
                if label[y]==idx and y not in prev:prev[y]=x;todo.append(y)
        raise AssertionError('SCC path missing')
    for idx,component in enumerate(components):
        black=next((x for x in component if x>>top&1),None)
        if black is None:continue
        for x in component:
            for y in edges[x]:
                if label[y]!=idx or (x>>top&1) or (y>>top&1):continue
                nontrivial+=1
                if witness is None:
                    walk=[x]+path(y,black,idx)+path(black,x,idx)[1:]
                    assert walk[0]==walk[-1] and any(z>>top&1 for z in walk)
                    for a,b in zip(walk,walk[1:]):
                        assert b in edges[a]
                        for j in range(2,width):
                            assert ((b>>j)&1)==((30>>(4*(a>>j&1)+2*(a>>(j-1)&1)+(a>>(j-2)&1)))&1)
                    witness={'walk':walk,'profile':[z>>top&1 for z in walk[:-1]],
                             'period':len(walk)-1,'arbitrary_oldest_two':True}
    return {'strip_width':width,'nodes':len(nodes),'sccs':len(components),
            'zero_zero_edges_in_black_scc':nontrivial,'nonalternating_relaxation_witness':witness}

for w in range(4,15):
    out=analyze(w);reports.append(out)
    print(json.dumps({k:v for k,v in out.items() if k!='nonalternating_relaxation_witness'}),flush=True)
    if out['nonalternating_relaxation_witness'] is None:break
result={'reports':reports,'Lean_verified':False,'finite_white_ancestry_not_established_for_walks':True,
        'uniform_actual_rigidity_proved':False,'full_problem_solved':False,
        'seconds':round(time.monotonic()-start,3)}
(r/'equal-profile-strip.json').write_text(json.dumps(result,indent=2)+'\n')
