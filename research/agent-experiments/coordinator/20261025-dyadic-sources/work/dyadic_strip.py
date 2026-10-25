"""Test a uniform fixed-strip formula before attempting its formal proof."""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent
start=time.monotonic()
N=65536; D=20
a=1; channels=[0]*D; source_bits=[[] for _ in range(D)]
snapshots=[]; checks=0
def lin(x): return x^(x<<2)
for t in range(N):
    if t>0 and t&(t+1)==0:
        k=(t+1).bit_length()-1
        values=[x>>t&1 for x in channels]
        # Explicit, deliberately conservative uniform prediction:
        # depth d positive even contributes zero when k-1 >= d;
        # odd d contributes zero at every odd observation time; depth 0 contributes 1.
        assert values[0]==1
        for d,v in enumerate(values):
            if d%2: assert v==0; checks+=1
            elif d>0 and k-1>=d: assert v==0; checks+=1
        snapshots.append({'time':t,'k':k,'center':a>>t&1,'channels_by_right_depth':values,
                          'prefix_strip_parities':[sum(values[:w])%2 for w in [1,2,4,8,12,16,20]]})
    src=(a<<1)&~a
    for d in range(D):
        j=2*t+1-d
        b=int(j>=0 and src>>j&1)
        source_bits[d].append(b)
        channels[d]=lin(channels[d])^((b<<j) if j>=0 else 0)
    a=(a<<2)^((a<<1)|a)
period_checks=[]
for d in range(13):
    q=1<<d
    assert source_bits[d][:N-q] == source_bits[d][q:]
    assert source_bits[d][q-1] == int(d==0)
    period_checks.append({'right_depth':d,'power_two_period_bound':q,
                          'period_comparisons':N-q,'last_phase_source':source_bits[d][q-1]})
sampled_formula_checks=pointwise_zero_checks=0
for snap in snapshots:
    k=snap['k']; H=1<<(k-1)
    for d in range(0,D,2):
        r=d//2
        if H<=r: continue
        samples=[H-1+r-u for u in range(r+1) if u&r==u]
        vals=[source_bits[d][s] for s in samples]
        assert sum(vals)%2 == snap['channels_by_right_depth'][d]
        sampled_formula_checks+=1
        if d>0 and k-1>=d:
            assert not any(vals)
            pointwise_zero_checks+=len(vals)
out={'claim':'uniform candidate derived algebraically; only finite validation here; not Lean verified',
     'uniform_candidate':'For each fixed positive strip width W, the Rule90-propagated sources at right depths d<W contribute exactly 1 at center time 2^k-1 whenever k>=W. The unbounded remainder is unrestricted.',
     'depth_channel_formula':'For d=2r and H=2^(k-1)>r: C_d(2^k-1)=XOR_(u submask r) b_d(H-1+r-u); odd d have zero contribution.',
     'periodic_reduction':'If H is divisible by the source period and period divides 2^d, replace each sample by phase r-1-u. Every nonnegative phase is <r and hence outside the initial finite cone; only phase -1 remains. That phase is 0 for d>0 because Phi^(-1)(1) has every bit 1, and b_d=R_d AND NOT R_(d-1).',
     'limits':'Does not prove uncancelled signal in full center; deeper sources can cancel. Does not prove infinitely many zeros at dyadic-minus-one times. Does not solve P1.',
     'source_period_checks':period_checks,'dyadic_snapshots':snapshots,
     'predicted_zero_channel_checks':checks,'sampled_formula_checks':sampled_formula_checks,
     'pointwise_zero_checks':pointwise_zero_checks,'elapsed_seconds':time.monotonic()-start,
     'new_kernel_verified_declarations':0}
(root/'dyadic-strip.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'zero_channel_checks':checks,'elapsed_seconds':out['elapsed_seconds'],
                  'last_snapshots':snapshots[-3:]},indent=2))
