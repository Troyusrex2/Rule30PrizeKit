"""Independent right-edge packing checks of the exact Lean event predicate."""
from pathlib import Path
import json,math,time
root=Path(__file__).resolve().parent
start=time.monotonic()
rows=[1]
for _ in range(2047): rows.append(rows[-1]^((rows[-1]<<1)|(rows[-1]<<2)))
assert bytes(a>>t&1 for t,a in enumerate(rows))==(root/'center-65536.bin').read_bytes()[:2048]
records=[]; tested=binomial=0
for e in range(11):
    H=1<<e; n=2*H-1
    events=[]
    for d in range(e+1):
        for s in range(n):
            a=rows[s]
            b=(a>>d&1) and (d==0 or not(a>>(d-1)&1))
            if d%2: continue
            r=d//2; K=H-1-r; h=2*H-2-s
            mask=(K&h)==K
            if e<=7:
                assert mask==bool(math.comb(h,K)%2 if K<=h else 0)
                binomial+=1
            selected=mask and b
            assert bool(selected)==bool(d==0 and s==H-1)
            tested+=1
            if selected: events.append({'depth':d,'source_time':s})
    assert len(events)==1
    records.append({'e':e,'center_time':n,'sources':events})
out={'claim':'finite control of the exact, separately kernel-replayed predicate',
     'packing':'right-edge bit d; Phi(a)=a XOR ((a<<1) OR (a<<2))',
     'events_checked':tested,'binomial_mask_crosschecks':binomial,
     'records':records,'all_passed':True,'elapsed_seconds':time.monotonic()-start}
(root/'selected-events-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'events_checked':tested,'binomial_mask_crosschecks':binomial,'all_passed':True}))
