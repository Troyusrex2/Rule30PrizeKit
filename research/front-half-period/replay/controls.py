from pathlib import Path
import hashlib,json,time
ROOT=Path(__file__).resolve().parent
started=time.monotonic()
def step(w,p,k):return (w^((w<<1)|(w<<2)|(3 if p==0 else 1)))&((1<<k)-1)
def literal(w,p,k):
    def bit(j):
        if j>=0:return (w>>j)&1
        return (1-p) if j==-1 else p
    return sum((bit(i)^ (bit(i-1)|bit(i-2)))<<i for i in range(k))
def q(n):
    t=1;r=0
    while n>=t:
        t=t+(1<<(t+r));r+=1
    return r
checked=0
for w in range(1024):
    for p in range(2):
        code=(w<<3)|(5 if p==0 else 3)
        nxt=code^((code<<1)|(code<<2))
        assert (nxt&7)==(3 if p==0 else 5)
        assert nxt>>3 == w^((w<<1)|(w<<2)|(3 if p==0 else 1))
        for k in (1,3,7,10):assert step(w,p,k)==literal(w,p,k)
        checked+=1
cycles=[]
for k in range(1,19):
    size=1<<(k+1);seen=bytearray(size);maxperiod=0;count=0
    for state in range(size):
        if seen[state]:continue
        here=state;length=0
        while not seen[here]:
            seen[here]=1;length+=1
            w,p=here>>1,here&1
            here=(step(w,p,k)<<1)|(1-p)
        assert here==state # triangular map is a permutation, no transient
        assert length&(length-1)==0
        maxperiod=max(maxperiod,length);count+=1
    bound=(k+3)//2+q((k+2)//2)
    assert maxperiod <= 1<<bound
    cycles.append({'width':k,'states':size,'cycles':count,'maximum_period':maxperiod,'exponent':maxperiod.bit_length()-1,'proved_bound_exponent':bound})
    assert time.monotonic()-started<60
result={'passed':True,'anchor_controls':checked,'cycle_controls':cycles,'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
