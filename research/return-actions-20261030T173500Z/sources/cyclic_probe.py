from pathlib import Path
from itertools import product
import json
R=Path(__file__).resolve().parent
def section(word,b):
    out=[]
    for q in reversed(word):
        out.append(2 if b else (1 if q==2 else 0));b^=(q!=0)
    return tuple(reversed(out))
def period(w):
    for p in [1,2,4,8]:
        if p<=len(w) and all(w[i]==w[i%p] for i in range(len(w))):return p
def legal(w):return all(q!=1 or w[(i-1)%len(w)]==2 for i,q in enumerate(w))
out=[]
for P in [2,4,8]:
    seen={};fold=None;collision=None;count=0
    for w in product(range(3),repeat=P):
        if not legal(w) or sum(q!=0 for q in w)%2:continue
        count+=1;d=period(w)
        for b in [0,1]:
            v=section(w,b);e=period(v)
            assert legal(v)
            if e<d and fold is None:fold=dict(word=w,bit=b,section=v,old_period=d,new_period=e)
            key=(d,v)
            if key in seen and seen[key]!=(w,b) and collision is None:
                collision=dict(first=seen[key],second=(w,b),section=v,old_period=d,new_period=e)
            seen[key]=(w,b)
    out.append(dict(P=P,legal_root_even=count,period_drop=fold,same_period_collision=collision))
(R/'CYCLIC_PROBE.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
