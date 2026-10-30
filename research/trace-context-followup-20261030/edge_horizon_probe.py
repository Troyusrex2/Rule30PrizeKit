"""One preregistered test of a strong quantitative EdgeObservable shortcut."""
import json
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def packed_trace(x, r, last):
    ans = []
    for t in range(last + 1):
        ans.append((x >> (r + t)) & 1 if r + t >= 0 else 0)
        x ^= (x << 1) | (x << 2)
    return ans


def literal_trace(x, r, last):
    black = {r-i for i in range(x.bit_length()) if x >> i & 1}
    ans = []
    for _ in range(last + 1):
        ans.append(int(0 in black))
        lo, hi = min(black)-1, max(black)+1
        black = {p for p in range(lo, hi+1)
                 if ((p-1 in black) ^ ((p in black) or (p+1 in black)))}
    return ans


def main():
    start = time.monotonic()
    census = []
    witness = None
    for w in range(1, 19):
        r = w//2 - 1
        seen = {}
        for seed in range(1, 1 << w):
            if time.monotonic()-start > 30:
                raise TimeoutError("preregistered wall guard")
            signature = 0
            x = seed
            for t in range(2*w+1):
                bit = (x >> (r+t)) & 1 if r+t >= 0 else 0
                signature = (signature << 1) | bit
                x ^= (x << 1) | (x << 2)
            edge = r-seed.bit_length()+1
            previous = seen.get(signature)
            if previous is not None and previous[0] != edge:
                a, b = previous[1], seed
                ta, tb = packed_trace(a, r, 4*w), packed_trace(b, r, 4*w)
                assert ta == literal_trace(a, r, 4*w)
                assert tb == literal_trace(b, r, 4*w)
                assert ta[:2*w+1] == tb[:2*w+1]
                first = next((t for t, (u,v) in enumerate(zip(ta,tb)) if u != v), None)
                witness = dict(width=w, observer_r=r, seeds=[a,b],
                               physical_supports=[[r-i for i in range(w) if a >> i & 1],
                                                  [r-i for i in range(w) if b >> i & 1]],
                               left_edges=[previous[0],edge],
                               prefix_agreement_through=2*w,
                               first_disagreement_within_followup=first,
                               followup_last_time=4*w, traces=[ta,tb],
                               independent_literal_control=True)
                break
            seen.setdefault(signature, (edge, seed))
        # Post-hoc descriptive statistic on precisely the registered prefixes.
        ordered = sorted(seen.items())
        best = max(((2*w+1-(sa^sb).bit_length(), va[1], vb[1])
                    for (sa,va),(sb,vb) in zip(ordered,ordered[1:]) if va[0] != vb[0]),
                   default=(0,None,None))
        census.append(dict(width=w, processed_seeds=seed, distinct_traces=len(seen),
                           complete=witness is None,
                           posthoc_max_unequal_edge_common_prefix_bits=best[0],
                           max_prefix_seed_pair=best[1:]))
        if witness is not None:
            break
    out = dict(status="linear_horizon_refuted" if witness else "finite_non_refutation_only",
               census=census, witness=witness, seconds=time.monotonic()-start,
               edge_observable_resolved=False)
    (ROOT/'edge-horizon-result.json').write_text(json.dumps(out, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(status=out['status'], witness=witness, seconds=out['seconds'])))


if __name__ == '__main__':
    main()
