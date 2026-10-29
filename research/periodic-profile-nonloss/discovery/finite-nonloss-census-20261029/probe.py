from pathlib import Path
import json,hashlib,time,collections
ROOT=Path(__file__).resolve().parent;started=time.monotonic()
WIDTH=24
def step(w,k):return (w^((w<<1)|(w<<2)))&((1<<k)-1)
def profile_exponents(orbit,k):
    size=len(orbit);assert size and size&(size-1)==0
    remaining=(1<<k)-1;result=[0]*k;exponent=size.bit_length()-1
    while size>1 and remaining:
        half=size//2;changed=0
        for j in range(half):changed|=orbit[j]^orbit[j+half]
        required=changed&remaining
        bits=required
        while bits:
            b=bits&-bits;result[b.bit_length()-1]=exponent;bits^=b
        remaining&=~required;size=half;exponent-=1
    return result
def oracle(orbit,k):
    result=[]
    for b in range(k):
        p=1
        while any(((orbit[t]^orbit[(t+p)%len(orbit)])>>b)&1 for t in range(len(orbit))):p*=2
        result.append(p.bit_length()-1)
    return result
assert profile_exponents([int(t%8==0)|(int(t%2==0)<<1) for t in range(8)],2)==[3,1]
control_count=0
for w in range(256):
    orbit=[];here=w
    while not orbit or here!=w:orbit.append(here);here=step(here,8)
    assert profile_exponents(orbit,8)==oracle(orbit,8)
    for state in orbit:
        literal=sum((((state>>b)&1)^(((state>>(b-1))&1 if b>=1 else 0)|((state>>(b-2))&1 if b>=2 else 0)))<<b for b in range(8))
        assert literal==step(state,8)
    control_count+=1
size=1<<WIDTH;seen=bytearray(size);states=0;cycles=0;maxperiod=0;counter=None;hist=collections.Counter();checked_oracles=0
for w in range(size):
    if seen[w]:continue
    orbit=[];here=w
    while not seen[here]:seen[here]=1;states+=1;orbit.append(here);here=step(here,WIDTH)
    assert here==w
    exps=profile_exponents(orbit,WIDTH);cycles+=1;maxperiod=max(maxperiod,len(orbit))
    if checked_oracles<16:
        assert exps==oracle(orbit,WIDTH);checked_oracles+=1
    for b in range(1,WIDTH):
        hist[(exps[b-1],exps[b])]+=1
        if exps[b]<exps[b-1]:
            counter={'initial_word':w,'width':WIDTH,'cycle_length':len(orbit),'older_diagonal':b-1,'new_diagonal':b,'older_exponent':exps[b-1],'new_exponent':exps[b],'all_exponents':exps,'orbit':orbit}
            break
    if counter:break
    if cycles%256==0:
        assert time.monotonic()-started<60
        print(json.dumps({'states':states,'cycles':cycles,'seconds':time.monotonic()-started}),flush=True)
complete=counter is None and states==size
result={'scope':'Python discovery, not Lean proof','width':WIDTH,'complete_census':complete,'states':states,'cycles':cycles,'max_period':maxperiod,'counterexample':counter,'synthetic_detection_control':True,'literal_small_controls':control_count,'full_oracle_controls':checked_oracles,'adjacent_exponent_histogram':{str(k):v for k,v in sorted(hist.items())},'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('counterexample','adjacent_exponent_histogram')},indent=2))
if counter:print(json.dumps({k:v for k,v in counter.items() if k!='orbit'}))
