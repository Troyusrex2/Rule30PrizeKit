"""Reuse P<=32; no extrapolation from the finite sample."""
from pathlib import Path
from collections import deque,Counter
import json,time
R=Path(__file__).resolve().parent;start=time.monotonic()
def sec(w,b):
    out=[]
    for q in reversed(w):out.append(2 if b else (1 if q==2 else 0));b^=q!=0
    return tuple(reversed(out))
def lc(bits):
    # Exact degree of the periodic word's minimal annihilator (X+1)^L.
    n=len(bits);a=sum(v<<i for i,v in enumerate(bits));L=0
    while a:
        a^=((a<<1)&((1<<n)-1))|(a>>(n-1));L+=1
        assert L<=n
    return L
out=[]
for P in [2,4,8,16,32]:
    root=(2,)*P;paths={root:(1,)};queue=deque([root]);spec=Counter();tuples=Counter()
    while queue:
        w=queue.popleft();c=lc([q==2 for q in w]);b=lc([q==1 for q in w]);f=lc([q!=0 for q in w])
        spec[c]+=1;tuples[c,b,f]+=1
        if sum(q!=0 for q in w)%2:continue
        for bit in [0,1]:
            v=sec(w,bit)
            if v not in paths:paths[v]=paths[w]+(bit,);queue.append(v)
    out.append(dict(P=P,states=len(paths),C_linear_complexities=sorted(spec),
        triples=sorted([dict(C=c,B=b,flip=f,count=n) for (c,b,f),n in tuples.items()],key=lambda x:(x['C'],x['B'],x['flip']))))
g=(0,0,0,2,1,2,2,2)
result=dict(results=out,bad_legal_word='AAACBCCC',bad_C_lc=lc([q==2 for q in g]),
    seconds=time.monotonic()-start,scope='Existing source graphs only; a candidate invariant diagnostic, no theorem for all P.')
(R/'SPECTRAL_ANCESTRY.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(spectra=[dict(P=x['P'],C=x['C_linear_complexities']) for x in out],bad_C_lc=result['bad_C_lc'],seconds=result['seconds'])))
