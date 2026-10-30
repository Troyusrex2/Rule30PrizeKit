from pathlib import Path
from itertools import combinations
import json,time
ROOT=Path(__file__).resolve().parent
def step(r):return (r>>1)^(r|(r<<1))
def trace(r,n):
    a=[]
    for t in range(2*n):
        if t%2==0:a.append(r&1)
        r=step(r)
    return a
def initial(W,a,free,pivots):
    r=1<<(W-1)
    for j,pos in enumerate(free):r|=((a>>j)&1)<<pos
    for t in pivots:
        q=r
        for _ in range(t):q=step(q)
        if not q&1:r^=1<<t
    assert all(trace(r,len(pivots))[k] for k in range(len(pivots)))
    return r
def mono_masks(n,d):
    for degree in range(d+1):
        for chosen in combinations(range(n),degree):yield sum(1<<j for j in chosen)
def monomial_table(mask,n):return sum(1<<a for a in range(1<<n) if a&mask==mask)
def solve(W,cap=45):
    start=time.monotonic();pivots=list(range(0,W-1,2));free=[j for j in range(W-1) if j not in pivots]
    n=len(free);N=2*W+4;viol=[0]*N;starts=[]
    for a in range(1<<n):
        r=initial(W,a,free,pivots);starts.append(r);tr=trace(r,N)
        for i,b in enumerate(tr):
            if not b:viol[i]|=1<<a
    assert all(viol[i]==0 for i in range(len(pivots)))
    if W<=10:
        survivors=[r for r in range(1<<(W-1),1<<W) if all(trace(r,len(pivots)))]
        assert sorted(survivors)==sorted(starts)
    target=(1<<(1<<n))-1;basis={};terms=[];selected=None;degrees=[]
    for d in range(4):
        masks=list(mono_masks(n,d));masks=[m for m in masks if m.bit_count()==d]
        for m in masks:
            table=monomial_table(m,n)
            for i,f in enumerate(viol):
                if time.monotonic()-start>cap:
                    return {'width':W,'status':'timeout_partial','free_bits':n,'degrees':degrees,'seconds':time.monotonic()-start}
                v=f&table
                if not v:continue
                pos=len(terms);terms.append((m,i));proof=1<<pos
                while v:
                    p=v.bit_length()-1
                    if p not in basis:basis[p]=(v,proof);break
                    bv,bp=basis[p];v^=bv;proof^=bp
        v=target;proof=0
        while v:
            p=v.bit_length()-1
            if p not in basis:break
            bv,bp=basis[p];v^=bv;proof^=bp
        degrees.append({'multiplier_degree':d,'span_rank':len(basis),'constant_in_span':v==0})
        if not v:
            selected=[terms[j] for j in range(len(terms)) if (proof>>j)&1]
            check=0
            for m,i in selected:check^=viol[i]&monomial_table(m,n)
            assert check==target
            return {'width':W,'status':'certificate_found','free_bits':n,'free_depths':[j+1 for j in free],
              'pins':N,'minimum_multiplier_degree':d,'selected_terms':[{'free_variable_mask':m,'pin':i} for m,i in selected],
              'degree_progress':degrees,'all_assignments_verified':1<<n,'seconds':time.monotonic()-start}
    return {'width':W,'status':'no_certificate_with_multiplier_degree_at_most3','free_bits':n,'degrees':degrees,'seconds':time.monotonic()-start}
def main():
    records=[]
    for W in range(4,21,2):
        r=solve(W);records.append(r)
        (ROOT/'boolean-certificate-results.json').write_text(json.dumps(records,indent=2)+'\n')
        print('width',W,r['status'],'degree',r.get('minimum_multiplier_degree'),'terms',len(r.get('selected_terms',[])),
              'seconds',round(r['seconds'],3),flush=True)
if __name__=='__main__':main()
