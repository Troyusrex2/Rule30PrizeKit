from pathlib import Path
import time,json,hashlib,psutil
ROOT=Path(__file__).resolve().parent

def integrate(g,p,initial):
    # Inclusive prefix XOR; shift1 converts it to the running XOR at time t.
    mask=(1<<p)-1;v=g;shift=1
    while shift<p:v^=v<<shift;v&=mask;shift*=2
    z=(v<<1)&mask
    if initial:z^=mask
    if g.bit_count()%2:return z|((z^mask)<<p),2*p
    return z,p

def run():
    start=time.monotonic();max_period=1;patterns=0;exceptions=[];bad=[];checked=0;unknown=None
    histogram={}
    for code in range(1,1024,2):
        p=1;a=b=0;exponents=[0,0];profiles=[(0,1),(0,1)]
        for n in range(2,25):
            initial=(code>>(n-2))&1
            z,newp=integrate(a|b,p,initial)
            if newp>65536:unknown='period_cap';break
            if newp!=p:
                a|=a<<p;b|=b<<p
            a,b=b,z;p=newp;max_period=max(p,max_period)
            exponents.append(p.bit_length()-1);profiles.append((z,p))
        if unknown:break
        letters=[exponents[i+1]-exponents[i] for i in range(len(exponents)-1)]
        for j in range(len(letters)-4):
            if letters[j:j+5]==[1,1,0,1,1]:
                record={'code':code,'j':j,'base_exponent':exponents[j]}
                if exponents[j]>=2:bad.append(record)
                else:exceptions.append(record)
            if letters[j:j+4]==[1,1,0,1] and exponents[j]>=2:patterns+=1
        # Literal spatial recurrence, retaining enough columns for all 64 ticks.
        row=code;mask=(1<<25)-1
        for t in range(65):
            for n in range(2,25):
                z,period=profiles[n]
                assert (row>>(n-2))&1 == (z>>(t%period))&1,(code,n,t)
            row^=(row<<1)|(row<<2);row&=mask
        checked+=1;histogram[p]=histogram.get(p,0)+1
        if checked%32==0:
            assert psutil.Process().memory_info().rss<1024**3
            assert psutil.virtual_memory().available>2*1024**3
            if time.monotonic()-start>60:unknown='time_cap';break
    assert not bad,bad
    r={'checked_seeds':checked,'expected_seeds':512,'complete':checked==512 and unknown is None,'unknown':unknown,'max_prefix_period':max_period,'guarded_1101_occurrences':patterns,'guarded_11011_violations':bad,'small_clock_11011':exceptions,'final_period_histogram':histogram,'seconds':time.monotonic()-start,'kernel_verified':False,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'CENSUS.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='small_clock_11011'}))
if __name__=='__main__':run()
