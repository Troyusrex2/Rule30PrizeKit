from pathlib import Path
import time,json
ROOT=Path(__file__).resolve().parent
def step(r):return (r>>1)^(r|(r<<1))
def forced_code(b,N):
    r=sum(((b>>j)&1)<<(2*j+1) for j in range(b.bit_length()))
    a=[]
    for n in range(N+1):
        q=r
        for _ in range(2*n):q=step(q)
        x=1^(q&1)
        r|=x<<(2*n)
        a.append(1^x)
    q=r
    for t in range(2*N+1):
        if t%2==0:assert q&1
        q=step(q)
    return a
def anf(values):
    a=values.copy();B=(len(a)-1).bit_length()
    for j in range(B):
        for m in range(len(a)):
            if m&(1<<j):a[m]^=a[m^(1<<j)]
    return [m for m,v in enumerate(a) if v]
start=time.monotonic();data=[];bad1=None;bad2=None
for b in range(256):
    if time.monotonic()-start>30:raise TimeoutError('fixed dyadic code cap')
    a=forced_code(b,128);data.append(a)
    assert a[:3]==[0,b&1,b&1]
    assert a[3]==((((b>>1)&1)^((b>>2)&1)) if not b&1 else (((b>>1)&1)&((b>>2)&1)))
    for k in range(1,8):
        if a[1<<k]!=(b&1) and bad1 is None:bad1={'b':b,'k':k,'index':1<<k,'actual':a[1<<k],'expected':b&1}
        threshold=(1<<(k-1))-1
        if b.bit_length()<=threshold and a[(1<<k)-1] and bad2 is None:
            bad2={'b':b,'k':k,'index':(1<<k)-1,'support_length':b.bit_length(),'threshold':threshold,'actual':1}
polys={str(j):anf([a[j] for a in data]) for j in [1,2,3,4,7,8,15,16,31,32,63,64,127,128]}
result={'candidate1_counterexample':bad1,'candidate2_counterexample':bad2,'dyadic_anf_masks':polys,
 'inputs':256,'odd_indices_constructed':129,'seconds':time.monotonic()-start,
 'scope':'Exact finite Boolean completion; no uniform theorem inferred'}
(ROOT/'dyadic-code-result.json').write_text(json.dumps(result,indent=2)+'\n')
print('candidate1',bad1,'candidate2',bad2,'seconds',result['seconds'])
print('dyadic_polynomial_sizes',{j:len(v) for j,v in polys.items()})
