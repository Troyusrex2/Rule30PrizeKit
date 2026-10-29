from pathlib import Path
from collections import deque,Counter
import hashlib,json,time
ROOT=Path(__file__).resolve().parent;started=time.monotonic()
def period(w,q):
    for p in (1,2,4,8,16,32):
        if p>q:break
        if all(((w>>t)&1)==((w>>((t+p)%q))&1) for t in range(q)):return p
    raise AssertionError
def successor(a,b,q,initial):
    c=0;bit=initial
    for t in range(q):c|=bit<<t;bit^=((a|b)>>t)&1
    return c,bit==initial
def graph(q):
    seen={(0,0):0};nodes=[(0,0)];todo=deque([0]);edges=[];counter=None
    while todo:
        i=todo.popleft();a,b=nodes[i];targets=[]
        if period(b,q)<period(a,q):counter={'index':i,'a':a,'b':b,'period_a':period(a,q),'period_b':period(b,q)}
        for initial in (0,1):
            c,valid=successor(a,b,q,initial)
            literal=all(((c>>((t+1)%q))&1)==(((c>>t)&1)^(((a>>t)&1)|((b>>t)&1))) for t in range(q))
            assert valid==literal
            if not valid:targets.append(None);continue
            nxt=(b,c)
            if nxt not in seen:
                assert len(nodes)<5000
                seen[nxt]=len(nodes);nodes.append(nxt);todo.append(seen[nxt])
            targets.append(seen[nxt])
        edges.append(targets)
        assert time.monotonic()-started<60
    assert len(edges)==len(nodes)
    return {'q':q,'nodes':nodes,'edges':edges,'counterexample':counter,'period_pairs':{str(k):v for k,v in sorted(Counter((period(a,q),period(b,q)) for a,b in nodes).items())}}
graphs=[graph(q) for q in (2,4,8,16,32)]
result={'scope':'Python discovery only; finite q profile graphs, all spatial depths','graphs':graphs,'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'RESULTS.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
print(json.dumps({'graphs':[{'q':g['q'],'states':len(g['nodes']),'edges':sum(x is not None for row in g['edges'] for x in row),'counterexample':g['counterexample'],'period_pairs':g['period_pairs']} for g in graphs],'seconds':result['seconds']}))
