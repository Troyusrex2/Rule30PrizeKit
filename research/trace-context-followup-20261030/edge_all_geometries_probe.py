import json
import time
from pathlib import Path
from edge_horizon_probe import packed_trace,literal_trace

ROOT = Path(__file__).resolve().parent
start = time.monotonic()
census=[]
witness=None
timeout=False
for w in range(1,17):
    for c in range(w):
        seen={}
        for a in range(1,1 << w):
            if time.monotonic()-start > 60:
                timeout=True
                break
            row=a
            sig=0
            for t in range(2*w+1):
                sig=(sig << 1)|((row >> (c+t)) & 1)
                row ^= (row << 1)|(row << 2)
            height=a.bit_length()
            prev=seen.get(sig)
            if prev is not None and prev[0] != height:
                b=prev[1]
                ta,tb=packed_trace(a,c,4*w),packed_trace(b,c,4*w)
                assert ta == literal_trace(a,c,4*w)
                assert tb == literal_trace(b,c,4*w)
                assert ta[:2*w+1] == tb[:2*w+1]
                witness=dict(width=w,observer=c,seeds=[a,b],
                             left_edges=[c-height+1,c-prev[0]+1],
                             first_disagreement_within_followup=next(
                                 (t for t,(u,v) in enumerate(zip(ta,tb)) if u != v),None),
                             prefix_agreement_through=2*w,last_time_checked=4*w,
                             independent_literal_control=True,traces=[ta,tb])
                break
            seen.setdefault(sig,(height,a))
        census.append(dict(width=w,observer=c,processed_seeds=a,
                           complete=witness is None and not timeout,
                           distinct_prefixes=len(seen)))
        if witness or timeout:
            break
    if witness or timeout:
        break
out=dict(status='linear_horizon_refuted' if witness else
                'bounded_incomplete' if timeout else 'finite_non_refutation_only',
         witness=witness,census=census,seconds=time.monotonic()-start,
         edge_observable_resolved=False)
(ROOT/'edge-all-geometries-result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='census'}))
