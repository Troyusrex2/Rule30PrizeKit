"""Independent physical controls for the constructive even-coordinate decoder.

Finite cones validate the implementation/interpretation, not the open Q01
tail assertion. No random free sequence is assumed golden or admissible.
"""
from functools import lru_cache
import json
from pathlib import Path
import random


def packed_step(a):
    return (a >> 1) ^ (a | (a << 1))


def packed_run(a, t):
    for _ in range(t): a = packed_step(a)
    return a


def reconstruct_even(u, length):
    row = 0; free = []
    for d in range(length):
        odd = 1 ^ (packed_run(row, 2*d) & 1)
        row |= odd << (2*d)
        row |= ((u >> d) & 1) << (2*d+1)
        free.append(packed_run(row, 2*d+1) & 1)
    return row, free


def recursive_decode(u, length):
    """The proved causal recurrence, evaluated with exact shared prefixes."""
    free = []
    for d in range(length):
        s = tuple(free)
        @lru_cache(None)
        def pair(m, k):
            if m == 0: return 1, 0
            if m == 1: return 1, (s[k] if k < len(s) else 0)
            e, o = pair(m-1, k)
            ep, op = pair(m-2, k)
            en, _ = pair(m-1, k+1)
            return o ^ (e | ep), en ^ (o | op)
        free.append(((u >> d) & 1) ^ pair(2*d+2, 0)[0])
    return free


def main():
    rng = random.Random(302410)
    length = 32; physical = decoder = prefixes = 0
    inputs = [0, (1 << length)-1, 5, 6]
    inputs += [rng.getrandbits(length) for _ in range(60)]
    for u in inputs:
        packed, free = reconstruct_even(u, length)
        assert recursive_decode(u, length) == free
        decoder += length
        # Positions are actual left-half depths. Boundary depth0 is white.
        row = {m: (packed >> (m-1)) & 1 for m in range(1, 2*length+1)}
        for t in range(2*length):
            assert row[1] == (1 if t % 2 == 0 else free[t//2])
            for m in range(1, 2*length-t+1):
                assert row[m] == (packed_run(packed, t) >> (m-1)) & 1
                physical += 1
            old = {0: 0, **row}
            row = {m: (30 >> ((old[m+1] << 2) | (old[m] << 1) | old[m-1])) & 1
                   for m in range(1, 2*length-t)}
        for n in [0, 1, 7, 15, length]:
            low = u & ((1 << n)-1)
            other = low | (rng.getrandbits(length-n) << n)
            _, changed = reconstruct_even(other, length)
            assert changed[:n] == free[:n]
            prefixes += n
    report = {'all_passed': True, 'prescribed_even_words': len(inputs),
              'decoded_free_bits_compared_with_physical_pivots': decoder,
              'independent_physical_cells': physical, 'prefix_bit_comparisons': prefixes,
              'free_bit_horizon': length, 'initial_spatial_width': 2*length,
              'only_uncontaminated_causal_cones_compared': True,
              'arbitrary_free_bits_not_assumed_golden': True,
              'Lean_verified_by_this_script': False, 'Q01_proved': False,
              'full_problem_solved': False}
    out=Path(__file__).with_name('even-decode-controls.json')
    out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__': main()
