"""Physical controls for Quint and Gemini's audited skelPair reconstruction.

These finite controls are separate from the complete kernel replay.
"""
from functools import lru_cache
import json
from pathlib import Path
import random

HERE = Path(__file__).resolve().parent


def skeleton(s):
    @lru_cache(None)
    def pair(m, k):
        if m == 0: return 1, 0
        if m == 1: return 1, s[k]
        a, b = pair(m-1, k)
        na, _ = pair(m-1, k+1)
        p, q = pair(m-2, k)
        return b ^ (a | p), na ^ (b | q)
    return pair


def main():
    rng = random.Random(304800)
    physical = pivots = 0
    for _ in range(64):
        s = [rng.randrange(2) for _ in range(64)]
        pair = skeleton(s)
        width = 40
        row = {k: pair(k, 0)[0] for k in range(1, width+1)}
        for t in range(17):
            for k in range(1, width-t+1):
                assert row.get(k, 0) == pair(k, t//2)[t%2]
                physical += 1
            old = {0: 0, **row}
            row = {k: (30 >> ((old.get(k+1, 0) << 2) |
                             (old.get(k, 0) << 1) | old.get(k-1, 0))) & 1
                   for k in range(1, width+t+2)}
        for d in range(8):
            for k in range(4):
                altered = s.copy()
                altered[k+d] ^= 1
                other = skeleton(altered)
                assert pair(2*d+1, k)[0] == other(2*d+1, k)[0]
                assert pair(2*d+1, k)[1] != other(2*d+1, k)[1]
                assert pair(2*d+2, k)[0] != other(2*d+2, k)[0]
                pivots += 3
    report = {'all_passed': True, 'independent_physical_cells': physical,
        'finite_locality_and_pivot_checks': pivots, 'free_bit_examples': 64,
        'physical_time_range': [0, 16], 'initial_spatial_width': 40,
        'only_uncontaminated_causal_cones_compared': True,
        'arbitrary_free_bits_not_assumed_golden': True,
        'Lean_verified_by_this_script': False, 'Q01_proved': False,
        'full_problem_solved': False}
    (HERE/'skelpair-ad1748-controls.json').write_text(json.dumps(report, indent=2)+'\n',
        encoding='utf-8', newline='\n')
    print(json.dumps(report))


if __name__ == '__main__': main()
