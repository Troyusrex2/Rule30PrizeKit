"""Look for different-edge trace collisions with infinite periodic right tails.

Only finite observation prefixes are computed. Causality justifies truncating
the right tail beyond the horizon. No all-time equality follows from a match.
"""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent
H=128;maximum_edge_depth=7;maximum_period=6

def row(m,left,period,tail,horizon):
    origin=horizon+maximum_edge_depth+4
    a=(1<<(origin-m))|(left<<(origin-m+1))
    for p in range(1,horizon+2):
        if (tail>>((p-1)%period))&1:a|=1<<(origin+p)
    return origin,a

def trace(m,left,period,tail,horizon):
    origin,a=row(m,left,period,tail,horizon)
    sig=0
    for t in range(horizon+1):
        sig|=((a>>origin)&1)<<t
        a=(a<<1)^(a|(a>>1))
    return sig

def scalar_trace(m,left,period,tail,horizon):
    def initial(p):
        if p < -m:return 0
        if p==-m:return 1
        if p<=0:return (left>>(p+m-1))&1
        return (tail>>((p-1)%period))&1
    rows={p:initial(p) for p in range(-m-horizon-2,horizon+3)}
    sig=0
    for t in range(horizon+1):
        sig|=rows[0]<<t
        lo=-m-horizon-2+t+1;hi=horizon+3-t-1
        rows={p:int(rows[p-1] != (rows[p] or rows[p+1])) for p in range(lo,hi)}
    return sig

started=time.monotonic();records=[];perdepth={};controls=0
for m in range(1,maximum_edge_depth+1):
    perdepth[m]=0
    for p in range(1,maximum_period+1):
        for left in range(1<<m):
            for tail in range(1<<p):
                sig=trace(m,left,p,tail,H)
                key=int(format(sig,f'0{H+1}b')[::-1],2)
                records.append((key,m,left,p,tail,sig));perdepth[m]+=1
                if (left*7+tail*11+p*13+m*17)%211==0:
                    # Scalar physical evolution and a doubled horizon use
                    # separate initial cutoffs and must reproduce the prefix.
                    assert scalar_trace(m,left,p,tail,32)==sig&((1<<33)-1)
                    assert trace(m,left,p,tail,2*H)&((1<<(H+1))-1)==sig
                    controls+=1

records.sort();longest=-1;witness=None;collisions={}
for a,b in zip(records,records[1:]):
    if a[1]==b[1]:continue
    common=H+1-(a[0]^b[0]).bit_length()
    if common>longest:
        longest=common;witness=[a[1:5],b[1:5]]
    if common==H+1:collisions.setdefault(tuple(sorted((a[1],b[1]))),[a[1:5],b[1:5]])
result={'finite_observation_only':True,'initial_right_tails_are_infinite_periodic':True,
        'all_time_collision_proved':False,'full_problem_solved':False,
        'horizon':H,'maximum_edge_depth':maximum_edge_depth,'maximum_spatial_period':maximum_period,
        'parameterized_starts':len(records),'per_depth':perdepth,
        'scalar_and_doubled_horizon_controls':controls,'longest_different_edge_common_prefix':longest,
        'maximal_witness':witness,'full_horizon_collisions':[{'depths':k,'witness':v} for k,v in collisions.items()],
        'seconds':time.monotonic()-started}
(root/'periodic-tail-trace.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
