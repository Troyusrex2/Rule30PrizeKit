"""Exact inverse-profile test for the one newly found period8 driver."""
from pathlib import Path
from collections import deque
import json,time
R=Path(__file__).resolve().parent;start=time.monotonic();P=8;M=255
word='CBCABCCB';c=sum((q=='C')<<t for t,q in enumerate(word))
def D(x):return x^((x>>1)|((x&1)<<7))
starts=[]
for h in range(256):
    if all(q=='C' or ((h>>t)&1)==(q=='B') for t,q in enumerate(word)) and not h&~D(c):starts.append((c,h))
def predecessors(v):
    a,b=v;d=D(a);e=D(b)
    if b&~d:return []
    base=d&~b
    if base&~e:return []
    free=b&e;g=free;out=[]
    while True:
        out.append((b,base|g))
        if g==0:return out
        g=(g-1)&free
color={};parent={};cycle=None;found_start=None;memo={}
def visit(v,origin):
    global cycle,found_start
    color[v]=1
    for w in predecessors(v):
        if color.get(w,0)==0:
            parent[w]=v
            if visit(w,origin):return True
        elif color.get(w)==1:
            path=[v]
            while path[-1]!=w:path.append(parent[path[-1]])
            path.reverse();cycle=path;found_start=origin;return True
    color[v]=2
    memo[v]=1+max([memo[w] for w in predecessors(v)],default=0)
    return False
for v in starts:
    if color.get(v,0)==0 and visit(v,v):break
out=dict(driver=word,period=P,initial_pairs=starts,states_visited=len(color),cycle=cycle,
    max_finite_chain=None if cycle else max(memo.values(),default=0),seconds=time.monotonic()-start)
if cycle:
    for i,v in enumerate(cycle):assert cycle[(i+1)%len(cycle)] in predecessors(v)
    lead=[];u=cycle[0]
    while u!=found_start:lead.append(u);u=parent[u]
    lead.append(found_start);lead.reverse()
    out['path_to_cycle']=lead
out['scope']='One categorical driver, period8 only. A cycle would supply a genuine infinite periodic left ancestry; absence only rejects that period8 ancestry.'
(R/'PROFILE_ANCESTRY.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(out))
