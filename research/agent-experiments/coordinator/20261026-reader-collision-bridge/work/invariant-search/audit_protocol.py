"""Independent scalar checks of cyclic carries and every accumulated ICE fact.
This does not establish an invariant; every reported candidate still failed.
"""
from pathlib import Path
from functools import lru_cache
import json
r=Path(__file__).resolve().parent
dfa=json.loads((r/'learned-reader.json').read_bytes())['dfa']
def unpack(a):return [(a>>j)&1 for j in [3,2,1,0]]
def pack(a,b,c,d):return a*8+b*4+c*2+d
def convert(w,c):
    a,b=c>>1,c&1;out=[]
    for symbol in w:
        u,v,up,vp=unpack(symbol);out.append(pack(v,a,vp,b))
        a=(30>>((a<<2)|(u<<1)|v))&1;b=(30>>((b<<2)|(up<<1)|vp))&1
    return tuple(out),(a<<1)|b
def safe(q,w):return q!=15 or any(unpack(a)[1]!=unpack(a)[3] for a in w)
def implied(q,w,qp,wp):
    return any(dfa['transitions'][q][c]==qp and convert(w,c)==(tuple(wp),c) for c in range(4))
def negative_valid(q,w):
    if not safe(q,w):return True
    for c in range(4):
        out,last=convert(w,c);qp=dfa['transitions'][q][c]
        if last==c and not safe(qp,out):return True
    return False
graphs={};graph_controls=0;blocked=0
for P in [2,4,8,16]:
    states=json.loads((r/f'clock-product-{P}-graph.json').read_bytes())['states'];index={tuple(s) for s in states};graphs[P]=index
    for u,v,up,vp,q in states:
        assert (v==vp)==(q in dfa['accepting'])
        w=tuple(pack((u>>t)&1,(v>>t)&1,(up>>t)&1,(vp>>t)&1) for t in range(P))
        for c in range(4):
            out,last=convert(w,c)
            if last!=c:blocked+=1;continue
            av=sum(unpack(a)[0]<<t for t,a in enumerate(out));aw=sum(unpack(a)[1]<<t for t,a in enumerate(out))
            bv=sum(unpack(a)[2]<<t for t,a in enumerate(out));bw=sum(unpack(a)[3]<<t for t,a in enumerate(out))
            assert (av,aw,bv,bw,dfa['transitions'][q][c]) in index;graph_controls+=1
def positive_valid(q,w):
    if q==0 and all(a==0 for a in w):return True
    P=len(w)
    if P not in graphs:return False
    values=[sum(unpack(a)[i]<<t for t,a in enumerate(w)) for i in range(4)]
    return (*values,q) in graphs[P]
reports=[]
for name in ['ice-samples.json','ice-safe-samples.json']:
    p=json.loads((r/name).read_bytes())
    assert not ({(q,tuple(w)) for q,w in p['positive']} & {(q,tuple(w)) for q,w in p['negative']})
    assert all(positive_valid(q,w) for q,w in p['positive'])
    assert all(negative_valid(q,w) for q,w in p['negative'])
    assert all(implied(q,w,qp,wp) for q,w,qp,wp in p['implications'])
    reports.append({'file':name,'positive':len(p['positive']),'negative':len(p['negative']),
                    'implications':len(p['implications']),'all_semantic_checks_passed':True})
for name in ['ice-tree-samples.json','ice-dyadic-samples.json','ice-sym-dyadic-samples.json','ice-typed-samples.json']:
    if not (r/name).exists():continue
    p=json.loads((r/name).read_bytes());trees=p['trees'];reverse={tuple(v):i for i,v in enumerate(trees) if i>=16}
    for i,t in enumerate(trees):
        if i>=16:assert len(t)==2 and all(0<=c<i for c in t)
    @lru_cache(maxsize=None)
    def leaves(i):
        if i<16:return (i,)
        a,b=trees[i];x=leaves(a)+leaves(b)
        assert len(x)<100000
        return x
    for q,t in p['positive']:assert positive_valid(q,leaves(t))
    for q,t in p['negative']:assert negative_valid(q,leaves(t))
    for q,a,qp,b in p['implications']:assert implied(q,leaves(a),qp,leaves(b))
    reports.append({'file':name,'positive':len(p['positive']),'negative':len(p['negative']),
                    'implications':len(p['implications']),'all_semantic_checks_passed':True,
                    'maximum_sample_leaf_count':max(len(leaves(t)) for _,t in p['positive']+p['negative'])})
out={'passed':True,'cyclic_extension_edges_checked':graph_controls,'noncyclic_carries_rejected':blocked,
     'sample_audits':reports,'Lean_verified':False,'invariant_found':False,'full_problem_solved':False}
(r/'protocol-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out),flush=True)
