from pathlib import Path
import json,time,hashlib,collections
ROOT=Path(__file__).resolve().parent;started=time.monotonic()
def step(w,k):return (w^((w<<1)|(w<<2)))&((1<<k)-1)
def exponents(orbit,k):
    size=len(orbit);assert size and size&(size-1)==0
    remaining=(1<<k)-1;out=[0]*k;e=size.bit_length()-1
    while size>1 and remaining:
        half=size//2;changed=0
        for j in range(half):changed|=orbit[j]^orbit[j+half]
        bits=changed&remaining
        while bits:
            bit=bits&-bits;out[bit.bit_length()-1]=e;bits^=bit
        remaining&=~changed;size=half;e-=1
    return out
def no00(orbit,k):
    mask=(1<<k)-1;has=0
    for i,w in enumerate(orbit):has|=(mask^w)&(mask^orbit[(i+1)%len(orbit)])
    return mask^has
def literal(orbit,k):
    es=[];flags=0
    for b in range(k):
        p=1
        while any(((orbit[t]^orbit[(t+p)%len(orbit)])>>b)&1 for t in range(len(orbit))):p*=2
        es.append(p.bit_length()-1)
        if all(((orbit[t]|orbit[(t+1)%len(orbit)])>>b)&1 for t in range(len(orbit))):flags|=1<<b
    return es,flags
assert exponents([int(t!=0) for t in range(16)],1)==[4] and no00([int(t!=0) for t in range(16)],1)==1
assert exponents([0,1],1)==[1] and no00([0,1],1)==1
for w in range(256):
    orbit=[];here=w
    while not orbit or here!=w:orbit.append(here);here=step(here,8)
    expected,flags=literal(orbit,8);assert exponents(orbit,8)==expected and no00(orbit,8)==flags
WIDTH=24;size=1<<WIDTH;seen=bytearray(size);states=cycles=0;counter=None;hist=collections.Counter()
for w in range(size):
    if seen[w]:continue
    orbit=[];here=w
    while not seen[here]:seen[here]=1;states+=1;orbit.append(here);here=step(here,WIDTH)
    assert here==w
    es=exponents(orbit,WIDTH);flags=no00(orbit,WIDTH);cycles+=1
    for b in range(WIDTH):
        if (flags>>b)&1:
            hist[es[b]]+=1
            if es[b]>3:
                word=sum(((s>>b)&1)<<t for t,s in enumerate(orbit))
                assert all(((word>>t)&1) or ((word>>((t+1)%len(orbit)))&1) for t in range(len(orbit)))
                assert any(((word>>t)&1)!=((word>>((t+8)%len(orbit)))&1) for t in range(len(orbit)))
                counter={'seed':w,'width':WIDTH,'diagonal_bit':b,'period_exponent':es[b],'whole_prefix_cycle':len(orbit),'orbit':orbit,'profile_word':word,'literal_scalar_checks_passed':True}
                break
    if counter:break
    if cycles%256==0:assert time.monotonic()-started<60
out={'scope':'bounded numerical census only; no general or Lean theorem','width':WIDTH,'complete':counter is None and states==size,'states':states,'cycles':cycles,'no00_exponent_histogram':dict(hist),'counterexample':counter,'scalar_controls':256,'synthetic_positive_and_negative_controls':True,'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'RESULTS.json').write_bytes((json.dumps(out,indent=2)+'\n').encode())
print(json.dumps({k:v for k,v in out.items() if k!='counterexample'}))
if counter:print(json.dumps({k:v for k,v in counter.items() if k not in ['orbit','profile_word']}))
