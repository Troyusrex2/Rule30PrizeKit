from pathlib import Path
import json,time,hashlib,psutil
ROOT=Path(__file__).resolve().parent
def B(n):
    d=n//2;threshold=1;q=0
    while threshold<=d:
        threshold+=1<<(threshold+q);q+=1
    return (n+1)//2+q
def run():
    started=time.monotonic();results=[]
    for width in range(1,23):
        count=1<<width;mask=count-1;visited=bytearray(count);hist={};witness=None;maxperiod=0
        for s in range(count):
            if visited[s]:continue
            at=s;length=0
            while not visited[at]:
                visited[at]=1;length+=1;at=(at^((at<<1)|(at<<2)))&mask
            assert at==s,'triangular map must be a permutation'
            assert length&(length-1)==0
            hist[length]=hist.get(length,0)+1
            if length>maxperiod:maxperiod=length;witness=s
        assert sum(k*v for k,v in hist.items())==count
        exponent=maxperiod.bit_length()-1
        assert exponent<=B(width-1),(width,exponent,B(width-1))
        r={'width':width,'states_exhausted':count,'max_period':maxperiod,'max_exponent':exponent,'half_rate_B':B(width-1),'max_cycle_representative':witness,'cycles':hist,'seconds':time.monotonic()-started}
        results.append(r);print(json.dumps({k:v for k,v in r.items() if k!='cycles'}),flush=True)
        assert psutil.Process().memory_info().rss<1024**3
        assert psutil.virtual_memory().available>2*1024**3
        if time.monotonic()-started>60:break
    (ROOT/'FINITE-ORDER.json').write_text(json.dumps({'results':results,'complete_to':results[-1]['width'],'kernel_verified':False,'seconds':time.monotonic()-started,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},indent=2)+'\n')
if __name__=='__main__':run()
