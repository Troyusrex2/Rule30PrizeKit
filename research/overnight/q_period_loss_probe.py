"""Finite falsification tests for diagonal period loss; no unbounded theorem.

The map is Q(x)[k]=x[k] XOR (x[k+1] OR x[k+2]), with a zero tail for
finite words. These are moving-diagonal observations, not the prize's center.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np


def q(x):
    return x ^ ((x >> 1) | (x >> 2))


def head_partition(rows, image):
    observed = rows & 1
    _, part = np.unique(observed, return_inverse=True)
    old_count = -1
    rounds = 0
    while int(part.max())+1 != old_count:
        old_count = int(part.max())+1
        _, part = np.unique(observed+2*part[image], return_inverse=True)
        rounds += 1
    return part, rounds


def finite_case(width):
    rows = np.arange(1 << width, dtype=np.int64)
    image = q(rows)
    part, rounds = head_partition(rows, image)
    power = image.copy()
    full_period = np.zeros(len(rows), dtype=np.int64)
    head_period = np.zeros(len(rows), dtype=np.int64)
    period = 1
    while (full_period == 0).any():
        full_period[(full_period == 0) & (power == rows)] = period
        head_period[(head_period == 0) & (part[power] == part)] = period
        if not (full_period == 0).any():
            break
        power = power[power]
        period *= 2
        assert period <= 1 << width
    bad = np.flatnonzero(full_period != head_period)
    good = ((rows | (rows >> 1)) & 1).astype(bool)
    old_count = -1
    while int(good.sum()) != old_count:
        old_count = int(good.sum())
        good &= good[image]
    return {'width': width, 'states': len(rows), 'head_partition_refinement_rounds': rounds,
        'period_loss_states': len(bad),
        'first_loss_state': int(bad[0]) if len(bad) else None,
        'constant_or_states': int(good.sum()),
        'constant_or_expected_count_matches': int(good.sum()) == 2*width-1}


def ring_q(x, width):
    right1 = (x >> 1) | ((x & 1) << (width-1))
    right2 = (right1 >> 1) | ((right1 & 1) << (width-1))
    return x ^ (right1 | right2)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-width', type=int, default=18)
    args = ap.parse_args()
    started = time.monotonic()
    cases = []
    for width in range(2, args.max_width+1):
        case = finite_case(width)
        cases.append(case)
        print(json.dumps(case), flush=True)
        if case['period_loss_states']:
            break
    # A spatially periodic infinite-right counterexample to dropping finiteness.
    orbit = [973, 58, 549, 446, 833, 177]
    assert all(ring_q(a, 10) == b for a, b in zip(orbit, orbit[1:]+orbit[:1]))
    assert all((a | (a >> 1)) & 1 for a in orbit)
    assert ring_q(ring_q(orbit[0], 10), 10) != orbit[0]
    report = {'finite_experiments_only': True, 'Lean_verified': False,
        'unbounded_head_period_theorem_proved': False, 'prize_problem_proved': False,
        'cases': cases, 'periodic_right_tail_counterexample': {
            'spatial_period': 10, 'temporal_cycle': orbit,
            'head_cycle': [a & 1 for a in orbit], 'head_or_next_always_one': True,
            'Q_squared_is_identity': False, 'Lean_verified': False},
        'seconds': round(time.monotonic()-started, 3)}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
