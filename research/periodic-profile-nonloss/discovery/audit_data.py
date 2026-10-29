from pathlib import Path
import json,time,hashlib,collections,sys
ROOT=Path(__file__).resolve().parent;start=time.monotonic()
source=ROOT/'attempt01-g913/RESULTS.json'
if not source.exists():source=ROOT/'PROFILE-GRAPH.json'
data=json.loads(source.read_text());reports=[]
for g in data['graphs']:
    q=g['q'];nodes=[tuple(p) for p in g['nodes']];edges=g['edges'];assert len(nodes)==len(set(nodes)) and nodes[0]==(0,0)
    assert len(edges)==len(nodes);parents={0:None};queue=collections.deque([0])
    while queue:
        i=queue.popleft()
        for bit,j in enumerate(edges[i]):
            if j is not None and j not in parents:parents[j]=(i,bit);queue.append(j)
    assert len(parents)==len(nodes)
    word_period=lambda w,p:all(((w>>t)&1)==((w>>((t+p)%q))&1) for t in range(q))
    for i,(a,b) in enumerate(nodes):
        assert 0<=a<1<<q and 0<=b<1<<q
        forcing=[((a>>t)&1)|((b>>t)&1) for t in range(q)]
        for initial,j in enumerate(edges[i]):
            if sum(forcing)%2:assert j is None;continue
            assert j is not None and 0<=j<len(nodes)
            newer,c=nodes[j];assert newer==b and c&1==initial
            for t in range(q):assert ((c>>((t+1)%q))&1)==(((c>>t)&1)^forcing[t])
        for e in range(q.bit_length()):
            p=1<<e
            assert not word_period(b,p) or word_period(a,p)
        if i==0:continue
        bits=[];at=i
        while parents[at] is not None:at,bit=parents[at];bits.append(bit)
        bits.reverse();width=len(bits);word=sum(bit<<j for j,bit in enumerate(bits));here=word
        for t in range(q):
            older=((here>>(width-2))&1) if width>=2 else 0
            assert older==((a>>t)&1) and ((here>>(width-1))&1)==((b>>t)&1)
            # Literal per-cell recurrence, independently of profile integration.
            here=sum((((here>>j)&1)^(((here>>(j-1))&1 if j>=1 else 0)|((here>>(j-2))&1 if j>=2 else 0)))<<j for j in range(width))
        assert here==word
    reports.append({'q':q,'nodes':len(nodes),'all_edges_checked':True,'period_inheritance_checked':True,'all_nonroot_finite_seed_realizations_checked':len(nodes)-1})
result={'passed':True,'scope':'independent numerical audit; Lean certificate is separate','graphs':reports,'seconds':time.monotonic()-start,'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'DATA-AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
