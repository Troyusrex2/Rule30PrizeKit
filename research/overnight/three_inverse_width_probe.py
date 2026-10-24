"""Exhaust finite C3w widths by enumerating the free temporal bits only.

Inverse cones give a bijection between W initial left cells and the first W
head observations. Only ceil(W/3) of those observations are free under the
(*,0,1) constraint. Enumerate those choices, reconstruct each initial row,
and forward check the remaining observations. This is discovery code, NOT
a Lean coverage proof. It proves nothing at unbounded width or all time.
"""

import argparse
import json
from pathlib import Path
from time import perf_counter

import numpy as np

from three_inverse_cone_probe import inverse, forward_scalar


def initial_rows(width):
    assert 1 <= width <= 63
    count = (width+2)//3
    modes = np.arange(1 << count, dtype=np.uint64)
    current = np.full(len(modes), sum(1 << t for t in range(width) if t % 3 == 2), dtype=np.uint64)
    for j in range(count):
        current |= ((modes >> j) & 1) << (3*j)
    previous = np.full(len(modes), sum(1 << t for t in range(width) if t % 3 == 1), dtype=np.uint64)
    rows = np.zeros(len(modes), dtype=np.uint64)
    for k in range(width):
        rows |= (current & 1) << k
        previous, current = current, ((current >> 1) ^ (current | previous)) & ((1 << (width-k-1))-1)
    return rows


def first_violation(row, guard=128):
    for t in range(guard):
        if t % 3 and row & 1 != int(t % 3 == 2):
            return t
        row = (row >> 1) ^ (row | (row << 1) | int(t % 3 == 1))
    return None


def controls():
    total = 0
    for width in range(1, 13):
        expected = [a for a in range(1 << width)
                    if all((forward_scalar(a, width) >> t) & 1 == int(t % 3 == 2)
                           for t in range(width) if t % 3)]
        actual = initial_rows(width)
        assert set(map(int, actual)) == set(expected)
        assert len(actual) == len(expected)
        total += 1 << width
    # Independently check both 64-bit limbs, including carries and high bits.
    rows = initial_rows(24)
    lo = rows.copy()
    hi = np.zeros(len(lo), dtype=np.uint64)
    exact = [int(a) for a in rows]
    mask = (1 << 64)-1
    for t in range(100):
        for j in (0, 1, 37, len(lo)-1):
            assert int(lo[j]) == exact[j] & mask
            assert int(hi[j]) == (exact[j] >> 64) & mask
        nlo = ((lo >> 1) | (hi << 63)) ^ (lo | (lo << 1) | int(t % 3 == 1))
        nhi = (hi >> 1) ^ (hi | (hi << 1) | (lo >> 63))
        lo, hi = nlo, nhi
        exact = [(a >> 1) ^ (a | (a << 1) | int(t % 3 == 1)) for a in exact]
    return {'exhaustive_small_rows': total, 'small_widths': 12,
            'limb_snapshots': 400, 'AllPassed': True}


def search(width):
    started = perf_counter()
    originals = initial_rows(width)
    lo = originals.copy()
    hi = np.zeros(len(lo), dtype=np.uint64)
    survivors = len(lo)
    history = []
    last = None
    for t in range(128):
        if t % 3:
            good = (lo & 1) == int(t % 3 == 2)
            if t >= width:
                history.append([t, int(good.sum())])
            assert t >= width or good.all()
            if not good.all():
                # Keep a witness with the latest checked violation.
                last = int(originals[np.flatnonzero(~good)[0]])
            originals, lo, hi = originals[good], lo[good], hi[good]
            if not len(lo):
                assert last is not None
                assert first_violation(last) == t
                return {'width_bound': width, 'free_mode_bits': (width+2)//3,
                        'inverse_rows_enumerated': survivors,
                        'all_finite_rows_excluded_within_checked_horizon': True,
                        'latest_first_violation': t, 'witness': str(last),
                        'survivor_history': history, 'seconds': perf_counter()-started}
        nlo = ((lo >> 1) | (hi << 63)) ^ (lo | (lo << 1) | int(t % 3 == 1))
        nhi = (hi >> 1) ^ (hi | (hi << 1) | (lo >> 63))
        lo, hi = nlo, nhi
    # Truncation affects no observed head bit before this guard. Do not
    # continue truncated rows beyond it or infer an all-time survivor.
    assert all(first_violation(int(a)) is None for a in originals)
    return {'width_bound': width, 'free_mode_bits': (width+2)//3,
            'inverse_rows_enumerated': survivors,
            'all_finite_rows_excluded_within_checked_horizon': False,
            'guard': 128, 'surviving_initial_rows': list(map(str, originals[:20])),
            'survivor_history': history, 'seconds': perf_counter()-started}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--widths', type=int, nargs='+', default=[24, 32, 40, 48, 56, 60])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = {'Lean_verified': False, 'C3w_proved': False, 'full_problem_solved': False,
              'coverage_proved_in_Lean': False, 'controls': controls(), 'results': []}
    for w in args.widths:
        result = search(w)
        report['results'].append(result)
        args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
        print(json.dumps(result), flush=True)
