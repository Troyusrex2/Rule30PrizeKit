"""Check exact preimage automata against independent literal Rule 30 unrolling."""
from pathlib import Path
from functools import lru_cache
import random,json
r=Path(__file__).resolve().parent
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa']
def convert(w,c):
    a,b=c//2,c%2;out=[]
    for v in w:
        u,x,up,xp=v//8,(v//4)%2,(v//2)%2,v%2
        out.append(x*8+a*4+xp*2+b)
        a=(30>>((a<<2)|(u<<1)|x))&1
        b=(30>>((b<<2)|(up<<1)|xp))&1
    return tuple(out),a*2+b
@lru_cache(maxsize=200000)
def safe(q,w,depth):
    if q==15 and all((a//4)%2==a%2 for a in w):return False
    if not depth:return True
    for c in range(4):
        out,last=convert(w,c)
        if last==c and not safe(reader['transitions'][q][c],out,depth-1):return False
    return True
def classify(m,q,w):
    s=m['starts'][q]
    for a in w:s=m['transitions'][s][a]
    return m['accept'][s]
rng=random.Random(260526);models=[];checked=0;diffs=0
for d in [1,2,3]:
    m=json.loads((r/f'exact-backward-depth-{d}.json').read_bytes());n=0
    for q in range(17):
        for a in range(16):
            for b in range(16):
                w=(a,b);assert classify(m,q,w)==safe(q,w,d);n+=1
    for _ in range(6000):
        q=rng.randrange(17);w=tuple(rng.randrange(16) for _ in range(rng.randrange(1,17)))
        result=classify(m,q,w);assert result==safe(q,w,d);n+=1
        if result!=safe(q,w,0):diffs+=1
    models.append({'depth':d,'states':len(m['accept']),'literal_unrolling_cases':n});checked+=n
assert diffs>0
out={'passed':True,'models':models,'literal_unrolling_cases':checked,
     'nontrivial_preimage_cases':diffs,'includes_nondyadic_clocks':True,'Lean_verified':False,
     'unbounded_fixed_point_found':False,'full_problem_solved':False}
(r/'backward-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out),flush=True)
