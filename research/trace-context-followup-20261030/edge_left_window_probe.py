import json
import time
from pathlib import Path
from edge_horizon_probe import packed_trace, literal_trace

ROOT = Path(__file__).resolve().parent
start = time.monotonic()
census = []
witness = None
for w in range(1, 19):
    seen = {}
    for seed in range(1, 1 << w):
        if time.monotonic()-start > 30:
            raise TimeoutError('preregistered wall guard')
        sig = 0
        x = seed
        for t in range(2*w+1):
            sig = (sig << 1) | ((x >> t) & 1)
            x ^= (x << 1) | (x << 2)
        edge = 1-seed.bit_length()
        prev = seen.get(sig)
        if prev is not None and prev[0] != edge:
            a, b = prev[1], seed
            ta, tb = packed_trace(a, 0, 4*w), packed_trace(b, 0, 4*w)
            assert ta == literal_trace(a, 0, 4*w)
            assert tb == literal_trace(b, 0, 4*w)
            assert ta[:2*w+1] == tb[:2*w+1]
            first = next((i for i,(u,v) in enumerate(zip(ta,tb)) if u != v),None)
            witness = dict(width=w, seeds=[a,b], left_edges=[prev[0],edge],
                           physical_supports=[[-i for i in range(w) if a >> i & 1],
                                              [-i for i in range(w) if b >> i & 1]],
                           first_disagreement_within_followup=first,
                           prefix_agreement_through=2*w, followup_last_time=4*w,
                           traces=[ta,tb], independent_literal_control=True)
            break
        seen.setdefault(sig, (edge,seed))
    ordered = sorted(seen.items())
    best = max(((2*w+1-(sa^sb).bit_length(), va[1],vb[1])
                for (sa,va),(sb,vb) in zip(ordered,ordered[1:]) if va[0] != vb[0]),
               default=(0,None,None))
    census.append(dict(width=w, processed_seeds=seed, distinct_traces=len(seen),
                       complete=witness is None,
                       max_unequal_edge_common_prefix_bits=best[0],
                       max_prefix_seed_pair=best[1:]))
    if witness:
        break
out = dict(status='linear_horizon_refuted' if witness else 'finite_non_refutation_only',
           census=census, witness=witness, seconds=time.monotonic()-start,
           edge_observable_resolved=False)
(ROOT/'edge-left-window-result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
