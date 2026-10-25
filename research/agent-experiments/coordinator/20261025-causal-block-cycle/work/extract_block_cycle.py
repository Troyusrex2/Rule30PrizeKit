"""Recover full block words and actual positions for the small solver core.
The finite combinatorial cycle is independently checked, not trusted to Z3.
"""
from pathlib import Path
from bisect import bisect_left,bisect_right
import hashlib,json
root=Path(__file__).resolve().parent
d=json.loads((root/'block-rank-distinct-onsets.json').read_text())
core=d['results'][-1]['unsat_core'];P=d['canonical_lag']
def phi(a):return a^((a<<1)|(a<<2))
def runs(d):
    out=[]
    while d:
        lo=(d&-d).bit_length()-1;n=((d>>lo)^((d>>lo)+1)).bit_length()-1
        out.append((lo,lo+n-1));d&=~(((1<<n)-1)<<lo)
    return out
def desc(a,b,block,phase):
    lo,hi=block
    def pair(i):return ((a>>i)&1)|(((b>>i)&1)<<1) if i>=0 else 0
    word=[pair(i) for i in range(lo,hi+1)]
    return {'phase':phase,'halo_left':pair(lo-1),'word':word,'halo_right':pair(hi+1)}
def feature(q):return [q['phase'],q['halo_left'],q['word'][0],q['word'][-1],q['halo_right']],len(q['word'])
rows=[1]
for _ in range(max(c['onset'] for c in core)+P+2):rows.append(phi(rows[-1]))
records=[]
for c in core:
    n=c['onset'];parent,target,kind=c['constraint']
    a=rows[n]<<P;b=rows[n+P];an=rows[n+2]<<P;bn=rows[n+P+2]
    old=runs(a^b);new=runs(an^bn);lo=[v[0] for v in old];hi=[v[1] for v in old]
    ps=[tuple(range(bisect_left(hi,l-4),bisect_right(lo,r))) for l,r in new]
    od=[desc(a,b,v,n%16) for v in old];nd=[desc(an,bn,v,(n+2)%16) for v in new]
    children={}
    for j,p in enumerate(ps):
        if len(p)==1:children.setdefault(p[0],[]).append(j)
    matches=[]
    for j,q in enumerate(nd):
        if list(feature(q))!=target:continue
        p=ps[j]
        if kind=='merge':ok=[list(feature(od[k])) for k in p]==parent
        else:ok=len(p)==1 and list(feature(od[p[0]]))==parent and (len(children[p[0]])>1)==kind
        if ok:
            matches.append({'parent_intervals':[old[k] for k in p],'child_interval':new[j],
                            'parent_descriptors':[od[k] for k in p],'child_descriptor':q,
                            'pure_child_intervals':[] if len(p)!=1 else [new[k] for k in children[p[0]]]})
    assert matches,c
    assert all((rows[n+i]>>(n+i)&1)==(rows[n+P+i]>>(n+P+i)&1) for i in range(3))
    records.append({'onset':n,'constraint_kind':kind,'matches':matches})
out={'finite_only':True,'Lean_verified':False,'lag':P,'records':records,
     'scope':'Each recorded match is reconstructed from actual canonical rows. Full-word equality must still be checked before claiming a full-word ordinal cycle.',
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(root/'block-cycle-witnesses.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
for r in records:
    print(json.dumps({'onset':r['onset'],'kind':r['constraint_kind'],'match_count':len(r['matches']),
                      'first':r['matches'][0]}))
