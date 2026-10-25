"""Independent physical checks of the uniform corner construction; no proof premise."""
from pathlib import Path
import json,random,time
start=time.monotonic();rng=random.Random(303020261025)
def shrink(w):return [w[i]^(w[i+1]|w[i+2]) for i in range(len(w)-2)]
def four(w):
    for _ in range(4):w=shrink(w)
    return w
table={n:four([(n>>i)&1 for i in range(9)])[0] for n in range(512)}
def q(w):return table[sum(x<<i for i,x in enumerate(w[:9]))]
def image(w):return [q(w[i:i+9]) for i in range(max(0,len(w)-8))]
def preimage(ys):
    tail=[0]*8
    for b in reversed(ys):tail=[b^q([0]+tail)]+tail
    return tail
def physical(w):
    row={i for i,x in enumerate(w) if x}
    for _ in range(4):
        row={i for i in range(min(row,default=0)-1,max(row,default=0)+2)
             if int(i-1 in row)^(int(i in row)|int(i+1 in row))}
    return [int(i in row) for i in range(4,len(w)-4)]
for n in range(512):
    w=[(n>>i)&1 for i in range(9)]
    assert image(w)==four(w)==physical(w)
    assert table[n]^table[n^1]==1
def gauge(w):return (sum((i+3)*x for i,x in enumerate(w))+sum(11*w[i]*w[i+1] for i in range(len(w)-1)))%23-11
rectangle=positive=negative=0
for size in range(65):
    for _ in range(12):
        ys=[rng.randrange(2) for _ in range(size)];mid=preimage(ys);m=size+2;c=q([0]+mid)
        assert image(mid)==ys and mid[-8:]==[0]*8
        actual=[]
        for a in range(2):
            for b in range(2):
                w=[a]+mid+[b]
                want=[a^c]+ys+[b]
                assert image(w)==four(w)==want
                if size<=16:assert image(w)==physical(w)
                rectangle+=1
                def H(v):return 7+gauge(v[1:])-gauge(v[:-1])
                def P(v):return gauge(v[4:4+m-1])-gauge(image(v))
                assert H(image(w))==H(w[4:4+m])+P(w[:-1])-P(w[1:])
                positive+=1
                actual.append(want)
        H=lambda v:int(bool(v[0] and v[-1]))
        corner=H([0]+ys+[0])+H([1]+ys+[1])-H([0]+ys+[1])-H([1]+ys+[0])
        assert corner==1
        negative+=1
out={'finite_only':True,'Lean_verified':False,'physical_all_nine_bit_inputs':512,
     'interior_lengths':list(range(65)),'realized_corner_words':rectangle,
     'nontrivial_coboundary_positive_checks':positive,'endpoint_product_negative_checks':negative,
     'seconds':time.monotonic()-start}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
