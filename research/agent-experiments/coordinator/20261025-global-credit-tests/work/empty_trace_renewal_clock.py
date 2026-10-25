"""Test an unbounded renewal mechanism using the existing exact Jen clock.
For an assumed finite constrained left row with last black depth m, a period-p
free-bit comparison run of C equalities starting at r forces
    2*(C-r-p) <= m.
Unbounded such values for the actual empty-right driver would prove CQ01Empty.
This script only measures finite data; it supplies no unbounded proof.
"""
from pathlib import Path
import hashlib,json,random,time
import numpy as np
root=Path(__file__).resolve().parent;started=time.monotonic();N=2**18
def free(initial,n):
    x=initial;out=[]
    for t in range(2*n-1):
        x=((x<<1)|int(t%2==0))^(x|(x>>1))
        if t%2==0:out.append(1-(x&1))
    return np.asarray(out,dtype=np.uint8)
def best_run(f,p):
    equal=f[p:]==f[:-p];bad=np.flatnonzero(~equal)
    ends=np.concatenate((bad,np.array([len(equal)],dtype=np.int64)))
    starts=np.concatenate((np.array([0],dtype=np.int64),bad+1))
    counts=ends-starts
    good=counts>0
    if not good.any():return None
    starts=starts[good];counts=counts[good];metric=2*(counts-starts-p)
    j=int(np.argmax(metric));k=int(np.argmax(counts))
    return {'p':p,'best_clock_lower_bound':int(metric[j]),'best_start':int(starts[j]),'best_comparison_count':int(counts[j]),
            'longest_start':int(starts[k]),'longest_comparison_count':int(counts[k])}
def scalar(f,p):
    records=[];i=0
    while i<len(f)-p:
        if f[i]!=f[i+p]:i+=1;continue
        start=i
        while i<len(f)-p and f[i]==f[i+p]:i+=1
        records.append((2*(i-start-start-p),start,i-start))
    return max(records,default=None,key=lambda v:v[0])
rng=random.Random(30302529);control_count=0
for n in [16,31,64,127]:
    for _ in range(8):
        f=np.asarray([rng.randrange(2) for _ in range(n)],dtype=np.uint8)
        for p in range(1,min(17,n)):
            a=best_run(f,p);b=scalar(f,p)
            assert (a is None)==(b is None)
            if a is not None:assert (a['best_clock_lower_bound'],a['best_start'],a['best_comparison_count'])==b
            control_count+=1
# Physical truth-table controls independent of the packed update.
for initial in [0,31,495,17]:
    actual=free(initial,48);state={i+1 for i in range(initial.bit_length()) if initial>>i&1};physical=[]
    for t in range(95):
        state={p for p in range(1,max(state|{1})+2) if (30>>((int((p-1 in state) if p>1 else t%2==0)<<2)|(int(p in state)<<1)|int(p+1 in state)))&1}
        if t%2==0:physical.append(int(1 not in state))
    assert physical==actual.tolist()
f=free(0,N);raw=f.tobytes();(root/'empty-free-262144.bin').write_bytes(raw)
periods=sorted(set(range(1,65))|{128,256,512,1024})
records=[best_run(f,p) for p in periods];records=[r for r in records if r is not None]
dyadic=[]
for k in range(6,19):
    end=2**k;rr=[best_run(f[:end],p) for p in [1,2,3,4,5,7,8,16,32] if p<end]
    rr=[r for r in rr if r is not None]
    dyadic.append({'free_bits':end,'best':max(rr,key=lambda r:r['best_clock_lower_bound']),
                   'period5':best_run(f[:end],5)})
known=free(31,4096);positive=best_run(known,2)
assert positive and positive['best_clock_lower_bound']>4000
def z_array(s):
    z=[0]*len(s);left=right=0
    for i in range(1,len(s)):
        if i<=right:z[i]=min(right-i+1,z[i-left])
        while i+z[i]<len(s) and s[z[i]]==s[i+z[i]]:z[i]+=1
        if i+z[i]-1>right:left,right=i,i+z[i]-1
    return z
# Search EVERY lag at a preregistered set of onsets, not just p<=1024.
# This remains a finite sample of onsets and does not claim all-string runs.
z_controls=0
for n in [16,31,64]:
    for _ in range(8):
        word=bytes(rng.randrange(2) for _ in range(n));z=z_array(word)
        for p in range(1,n):
            c=0
            while c+p<n and word[c]==word[c+p]:c+=1
            assert z[p]==c;z_controls+=1
onsets=sorted(set(range(8))|{2**k-1 for k in range(4,17)})
all_lag=[]
for r in onsets:
    z=z_array(raw[r:]);p=max(range(1,len(z)),key=lambda p:z[p]-p)
    all_lag.append({'start':r,'period':p,'comparison_count':z[p],
                    'clock_lower_bound':2*(z[p]-r-p)})
out={'finite_only':True,'Lean_verified':False,'initial_right_half':0,'free_bits':N,'physical_steps':2*N-1,
     'free_prefix80':''.join(map(str,f[:80].tolist())),'trace_sha256':hashlib.sha256(raw).hexdigest(),
     'run_detector_scalar_controls':control_count,'physical_CA_controls':4*95,
     'periods':records,'dyadic_records':dyadic,'known_absorbed_R31_positive_control':positive,
     'all_lags_at_selected_onsets':all_lag,'z_algorithm_scalar_controls':z_controls,
     'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'Finite measurements of exact Jen-clock bound 2*(C-r-p), obtained by taking ell=C+p-1 in the official free_bits_clock theorem. Every lag is tested at the listed selected onsets; all onsets are tested only for the listed fixed periods. Observed growth is not unboundedness, and a plateau does not prove boundedness.'}
(root/'empty-trace-renewal-clock.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'best_clock':max(records,key=lambda r:r['best_clock_lower_bound']),'best_all_lag':max(all_lag,key=lambda r:r['clock_lower_bound']),'last_dyadic':dyadic[-1],
                  'positive_control':positive,'seconds':out['seconds']}),flush=True)
