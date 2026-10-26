"""Finite free-outer-boundary graphs. No all-width or finite-start claim."""
from pathlib import Path
from math import gcd
import json, time

ROOT = Path(__file__).resolve().parent

def literal(s, c, u, width):
    bits=[(s>>j)&1 for j in range(width)]
    return sum(((c if j==0 else bits[j-1]) ^ (bits[j] | (u if j==width-1 else bits[j+1])))<<j
               for j in range(width))

def graph(word, width):
    size=1<<width; mask=size-1; p=len(word)
    adjacency=[]; labels=[]
    for phase,c in enumerate(word):
        for s in range(size):
            row=[]
            for u in (0,1):
                nxt=(((s<<1)|c) ^ (s|(s>>1)|(u<<(width-1)))) & mask
                assert nxt==literal(s,c,u,width)
                row.append(((phase+1)%p)*size+nxt)
            adjacency.append(tuple(row)); labels.append(c | (s&1))
    return adjacency, labels

def sccs(adj):
    # Iterative Tarjan, with a separate DFS frame stack and component stack.
    n=len(adj); index=[-1]*n; low=[0]*n; active=[False]*n
    stack=[]; count=0; components=[]
    for start in range(n):
        if index[start]>=0: continue
        index[start]=low[start]=count; count+=1
        stack.append(start);active[start]=True; frames=[[start,0]]
        while frames:
            v,i=frames[-1]
            if i<len(adj[v]):
                w=adj[v][i];frames[-1][1]+=1
                if index[w]<0:
                    index[w]=low[w]=count;count+=1
                    stack.append(w);active[w]=True;frames.append([w,0])
                elif active[w]:low[v]=min(low[v],index[w])
            else:
                frames.pop()
                if frames:low[frames[-1][0]]=min(low[frames[-1][0]],low[v])
                if low[v]==index[v]:
                    component=[]
                    while True:
                        w=stack.pop();active[w]=False;component.append(w)
                        if w==v:break
                    components.append(component)
    return components

def analyze(word, width):
    adj, labels=graph(word,width); components=sccs(adj)
    cyclic=[];bad=[]
    for component in components:
        if len(component)==1 and component[0] not in adj[component[0]]:continue
        members=set(component);distance={component[0]:0};todo=[component[0]]
        while todo:
            v=todo.pop()
            for w in adj[v]:
                if w in members and w not in distance:
                    distance[w]=distance[v]+1;todo.append(w)
        assert len(distance)==len(component)
        period=0
        for v in component:
            for w in adj[v]:
                if w in members:period=gcd(period,abs(distance[v]+1-distance[w]))
        assert period>0
        classes={};collision=None
        for v in component:
            key=distance[v]%period
            if key in classes and labels[v]!=labels[classes[key]]:
                collision=[classes[key],v]
                break
            classes[key]=v
        cyclic.append({'size':len(component),'period':period,'label_constant_on_classes':collision is None})
        if collision is not None:
            bad.append({'size':len(component),'period':period,'pair':collision})
    return {'word':''.join(map(str,word)),'width':width,'vertices':len(adj),
            'cyclic_scc_count':len(cyclic),'bad_scc_count':len(bad),
            'maximum_cyclic_scc_size':max((c['size'] for c in cyclic),default=0),
            'sufficient_reset_criterion':not bad,'first_bad_scc':bad[0] if bad else None}

def main():
    start=time.monotonic();results=[]
    for word in [(1,1,0),(1,0,1,1),(1,1,0,0),(1,0),(1,),(0,)]:
        for width in [1,2,3,4,5,6,8,10]:
            result=analyze(word,width);results.append(result)
            print(json.dumps(result),flush=True)
    (ROOT/'periodic-driver-probe.json').write_text(json.dumps({'scope':'finite free-boundary graphs only',
        'literal_rule_audit':'all edges at every tested width','elapsed_seconds':time.monotonic()-start,
        'results':results},indent=2)+'\n',encoding='utf-8')

if __name__=='__main__':main()
