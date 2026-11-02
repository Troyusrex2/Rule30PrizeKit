import collections,json,pathlib,time
ROOT=pathlib.Path(__file__).resolve().parent
SOURCE=ROOT/'period-two-language.json'
S={8,9,16,18,33,36,66,72,132,144}
def step(v,c,b):return (((v<<1)|c)^(v|(v>>1)|(b<<5)))&63
def bits(w):return ''.join(str(e[2]) for e in w)
def main():
    start=time.monotonic()
    saved=json.loads(SOURCE.read_text())['transitions']
    for v in range(64):
        check=[0,0]
        for a in (0,1):
            for b in (0,1):check[int(bool(v&3))]|=1<<step(step(v,1,a),0,b)
        assert check==saved[v]
    states=[(v,0,0) for v in range(64)];ids={s:i for i,s in enumerate(states)}
    adj=[];rev=[[] for _ in states];cursor=0
    while cursor<len(states):
        assert len(states)<=20000 and time.monotonic()-start<55
        v,h,n=states[cursor];out=int(bool(v&3));g=1-out;edges=[]
        old=[1-((h>>i)&1) for i in range(n)]
        if not ((out==0 and n and old[-1]==0) or (out==1 and n>=4 and all(old[-4:]))):
            h8=h|(g<<n);bad=n==7 and h8 not in S
            hn=h8 if n<7 else h8>>1;nn=min(n+1,7)
            for a in (0,1):
                for b in (0,1):
                    w=step(step(v,1,a),0,b);target=(w,hn,nn)
                    if target not in ids:
                        ids[target]=len(states);states.append(target);rev.append([])
                    j=ids[target];edge=[cursor,j,out,a,b,bad]
                    edges.append(edge);rev[j].append(cursor)
        adj.append(edges);cursor+=1
    # Iterative Kosaraju (no recursion or third-party graph library).
    seen=set();order=[]
    for root in range(len(states)):
        if root in seen:continue
        seen.add(root);stack=[(root,0)]
        while stack:
            v,i=stack[-1]
            if i<len(adj[v]):
                stack[-1]=(v,i+1);w=adj[v][i][1]
                if w not in seen:seen.add(w);stack.append((w,0))
            else:order.append(v);stack.pop()
    comp={};groups=[]
    for root in reversed(order):
        if root in comp:continue
        ci=len(groups);members=[];stack=[root];comp[root]=ci
        while stack:
            v=stack.pop();members.append(v)
            for w in rev[v]:
                if w not in comp:comp[w]=ci;stack.append(w)
        groups.append(members)
    def path(a,b,ci):
        parents={a:None};q=collections.deque([a])
        while b not in parents:
            v=q.popleft()
            for e in adj[v]:
                w=e[1]
                if comp[w]==ci and w not in parents:parents[w]=e;q.append(w)
        result=[]
        while b!=a:e=parents[b];result.append(e);b=e[0]
        return result[::-1]
    witness=None
    for ci,members in enumerate(groups):
        bads=[e for v in members for e in adj[v] if comp[e[1]]==ci and e[-1]]
        if not bads:continue
        first=bads[0];base=first[0];A=[first]+path(first[1],base,ci)
        for v in members:
            assert time.monotonic()-start<55
            for e in adj[v]:
                if comp[e[1]]!=ci:continue
                B=path(base,v,ci)+[e]+path(e[1],base,ci)
                if bits(A+B)!=bits(B+A):
                    # AB versus BA have equal length, distinct words, and both
                    # contain the known bad edge in A.
                    U=A+B;V=B+A
                    witness={'component_size':len(members),'base':states[base],
                             'length':len(U),'words':[bits(U),bits(V)],
                             'loops':[[{'before':states[e[0]],'after':states[e[1]],
                               'f':e[2],'inputs':e[3:5],'bad':e[5]} for e in loop] for loop in (U,V)]}
                    break
            if witness:break
        if witness:break
    report={'status':'counterexample' if witness else 'no-witness',
            'states':len(states),'edges':sum(map(len,adj)),
            'scc_sizes':sorted(map(len,groups),reverse=True)[:12],
            'seconds':time.monotonic()-start,'witness':witness}
    (ROOT/'recurrent-result.json').write_text(json.dumps(report,indent=2))
    print(json.dumps({k:v for k,v in report.items() if k!='witness'}))
    if witness:print(json.dumps({k:v for k,v in witness.items() if k!='loops'}))
if __name__=='__main__':main()
