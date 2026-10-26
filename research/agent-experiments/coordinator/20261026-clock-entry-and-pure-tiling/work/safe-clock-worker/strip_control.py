"""A bounded discriminating control, not a finite-white realization search."""
from pathlib import Path
import random,json
root=Path(__file__).resolve().parent
P=16;mask=(1<<P)-1
def bits(p):return [(p>>t)&1 for t in range(P)]
def has(p,pattern):
    bs=bits(p)
    return any(all(bs[(t+k)%P]==v for k,v in enumerate(pattern)) for t in range(P))
def height(p):
    hs=[0]
    for t,v in enumerate(bits(p)):hs.append(hs[-1]+((-1)**t)*(1-v))
    return {'drift':hs[-1],'span_one_clock':max(hs)-min(hs),'heights':hs}
def children(a,b):
    forcing=a|b
    if forcing.bit_count()%2:return []
    v=0;out=0
    for t in range(P):
        out|=v<<t
        v^=(forcing>>t)&1
    assert v==0
    return [out,out^mask]
def audit(ps):
    assert len(ps)==6
    for i in range(2,len(ps)):
        for t in range(P):
            assert ((ps[i]>>((t+1)%P))&1)==(((ps[i]>>t)&1)^(((ps[i-1]|ps[i-2])>>t)&1))
    assert not has(ps[-1],[0,0])
    assert all(has(p,[0,0]) and has(p,[1,1]) for p in ps[:-1])
    assert all(not has(p,[1,1,0,1,1]) and not has(p,[0,0,1,0,0]) for p in ps)
    assert all(height(p)['drift']!=0 or height(p)['span_one_clock']>2 for p in ps[-3:-1])
    return True
rng=random.Random(2042)
tried=0;found=None
for seed in range(4096):
    starts=[rng.randrange(1<<P),rng.randrange(1<<P)]
    if any(has(p,[1,1,0,1,1]) or has(p,[0,0,1,0,0]) for p in starts):continue
    layer=[starts]
    for depth in range(4):
        layer=[ps+[c] for ps in layer for c in children(ps[-2],ps[-1])
               if not has(c,[1,1,0,1,1]) and not has(c,[0,0,1,0,0])]
    for ps in layer:
        tried+=1
        if has(ps[-1],[0,0]):continue
        if not all(has(p,[0,0]) and has(p,[1,1]) for p in ps[:-1]):continue
        if not all(height(p)['drift']!=0 or height(p)['span_one_clock']>2 for p in ps[-3:-1]):continue
        assert audit(ps)
        found={'profiles_little_endian':ps,'time_order_words':[''.join(map(str,bits(p))) for p in ps],
               'heights':[height(p) for p in ps],'seed_index':seed}
        break
    if found:break
result={'period':P,'max_seeds':4096,'candidate_strips_tested':tried,'found':found,
        'scope':'Two arbitrary oldest drivers; four newest columns obey every cyclic Rule30 update. NO finite-white anchoring or minimal-counterexample assertion.'}
(root/'strip-control.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
