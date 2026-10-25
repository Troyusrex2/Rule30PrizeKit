"""Falsify a new first-return-depth prediction in the complete source sum."""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent
start=time.monotonic()
MAX_K=13
rows=[1]
for _ in range((1<<MAX_K)-1):rows.append(rows[-1]^((rows[-1]<<1)|(rows[-1]<<2)))
def source(d,s):
    if d==0:return 1
    return (rows[s]>>d&1) & (1^(rows[s]>>(d-1)&1))
def channel(H,r):
    q=r;parity=events=0
    while True:
        b=source(2*r,H-1+r-q)
        parity^=b;events+=b
        if q==0:break
        q=(q-1)&r
    return parity,events
records=[];total_terms=zero_below=even_rho_checks=0
for k in range(1,MAX_K+1):
    H=1<<(k-1);n=2*H-1
    diff=rows[H]^1
    rho=(diff&-diff).bit_length()-1
    channels=[channel(H,r) for r in range(H)]
    assert channels[0]==(1,1)
    assert sum(x for x,_ in channels)%2==(rows[n]>>n&1)
    assert all(events==0 for r,(p,events) in enumerate(channels) if 0<2*r<rho)
    zero_below+=sum(1 for r in range(1,H) if 2*r<rho)
    if rho%2==0 and rho//2<H:
        assert channels[rho//2][0]==1
        even_rho_checks+=1
    first_active=next((2*r for r,(p,events) in enumerate(channels) if r>0 and events),None)
    first_odd=next((2*r for r,(p,events) in enumerate(channels) if r>0 and p),None)
    records.append({'k':k,'H':H,'center_time':n,'return_disagreement_depth':rho,
                    'first_positive_active_depth':first_active,'first_positive_odd_channel':first_odd,
                    'center':rows[n]>>n&1,'total_active_events':sum(c for _,c in channels),
                    'odd_channels':sum(p for p,_ in channels),'even_rho_prediction_tested':rho%2==0 and rho//2<H,
                    'leading_channels':[{'depth':2*r,'parity':p,'events':c} for r,(p,c) in enumerate(channels) if c][:12]})
    total_terms+=sum(1<<r.bit_count() for r in range(H))
out={'finite_only':True,'hypothesis':'Positive source channels below rho vanish pointwise; if rho is even, channel rho has parity 1. rho is the least changed right-edge bit after H iterations.',
     'not_proved':'No uniform Lean proof of this new first-return prediction, and no control of total deep parity.',
     'controls':'All channel parities sum to actual seed center; all source samples are actual right-edge bits.',
     'records':records,'sampled_terms':total_terms,'zero_channels_below_rho':zero_below,
     'even_rho_checks':even_rho_checks,'all_passed':True,'elapsed_seconds':time.monotonic()-start}
bad=next(r for r in records if r['H']==16)
assert bad['return_disagreement_depth']==7 and bad['first_positive_active_depth']==14 and bad['first_positive_odd_channel']==18
out['counterexample_to_first_even_depth_after_odd_rho']={
    'H':16,'rho':7,'first_even_depth_above_rho':8,
    'actual_first_active_depth':14,'actual_first_odd_channel':18}
(root/'deep-channels.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['sampled_terms','even_rho_checks','all_passed','elapsed_seconds']}))
for r in records:print(json.dumps({k:v for k,v in r.items() if k!='leading_channels'}))
