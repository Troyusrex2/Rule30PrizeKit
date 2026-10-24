"""Nonlocal rank falsification restricted to exact restart pairs.

Outer=F^P(inner), P>=2, is checked rather than approximated by nested edges.
An appropriate rank for EVERY such lag would imply full nonperiodicity;
this finite experiment proves no rank and has no Lean theorem as output.
"""

import argparse
import json
from pathlib import Path
import random
from time import perf_counter

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

import paired_nonlocal_rank_probe as pair


def restart_pair(row, center, lag):
    outer = row
    for _ in range(lag):
        outer = pair.step(outer)
    return outer, row << lag, center+lag


def transition(row, center, lag):
    a, b, c = restart_pair(row, center, lag)
    assert pair.nested(a, b, c)
    na, nb = pair.step(a), pair.step(b)
    if (a >> c) & 1 != (b >> c) & 1 or (na >> (c+1)) & 1 != (nb >> (c+1)) & 1:
        return None
    old = pair.features(a, b, c)
    new = pair.features(na, nb, c+1)
    reward = int(((a >> c) & 1) != ((na >> (c+1)) & 1))
    return a, b, c, old, new, reward


def controls():
    rng = random.Random(202610240919)
    for _ in range(128):
        width = rng.randrange(3, 24)
        center = rng.randrange(1, width-1)
        lag = rng.randrange(1, 24)
        row = rng.getrandbits(width) | 1 | (1 << (width-1))
        x = {i-center for i in range(width) if row >> i & 1}
        for t in range(lag):
            x = {p for p in range(-center-t-1, width-center+t+1)
                 if ((p-1 in x) ^ ((p in x) or (p+1 in x)))}
        actual = sum(1 << (p+center+lag) for p in x)
        a, b, c = restart_pair(row, center, lag)
        assert a == actual and pair.nested(a, b, c)
        # Commutation: a new inner row gives exactly the updated pair,
        # after aligning the different packing origins.
        a2, b2, c2 = restart_pair(pair.step(row), center+1, lag)
        assert (a2, b2, c2) == (pair.step(a), pair.step(b), c+1)
    return {'independent_scalar_lag_cases': 128, 'restart_commutation_controls': 128,
            'AllPassed': True}


def holdout(coefficients, min_lag=2, max_lag=64):
    rng = random.Random(202610240920)
    accepted = failures = negative = 0
    worst = None
    for _ in range(30000):
        width = rng.randrange(3, 61)
        center = rng.randrange(1, width-1)
        lag = rng.randrange(min_lag, max_lag+1)
        row = rng.getrandbits(width) | 1 | (1 << (width-1))
        rec = transition(row, center, lag)
        if rec is None:
            continue
        a, b, c, old, new, reward = rec
        old_value, new_value = float(old @ coefficients), float(new @ coefficients)
        residual = new_value-old_value+reward
        accepted += 1
        negative += int(min(old_value, new_value) < -1e-7)
        if residual > 1e-7:
            failures += 1
            if worst is None or residual > worst['residual']:
                worst = {'inner_initial': str(row), 'inner_center_index': center,
                         'inner_width': width, 'lag': lag, 'residual': residual,
                         'reward': reward, 'old_score': old_value, 'new_score': new_value}
        if accepted == 512:
            break
    assert accepted == 512
    return {'actual_restart_transitions': accepted, 'descent_failures': failures,
            'negative_values': negative, 'worst': worst, 'tested_lags': [min_lag, max_lag]}


def run(max_width, max_lag, signed, output, min_lag=2):
    began = perf_counter()
    report = {'Lean_verified': False, 'full_problem_solved': False,
              'rank_proved': False, 'exact_restart_relation': True,
              'signed_sample_lower_bound_only': signed, 'features': pair.DIM,
              'controls': controls(), 'results': []}
    rows, rhs = [], []
    total = 0
    for width in range(3, max_width+1):
        count = flips = 0
        for middle in range(1 << (width-2)):
            row = (middle << 1) | 1 | (1 << (width-1))
            for center in range(1, width-1):
                for lag in range(min_lag, max_lag+1):
                    rec = transition(row, center, lag)
                    if rec is None:
                        continue
                    a, b, c, old, new, reward = rec
                    rows.append(new-old)
                    rhs.append(-reward)
                    if signed:
                        rows.extend((-old, -new))
                        rhs.extend((0, 0))
                    count += 1
                    flips += reward
        total += count
        if not rows:
            report['results'].append({'inner_width': width, 'lags': [min_lag, max_lag],
                                      'new_pairs': 0, 'total_pairs': 0,
                                      'status': None, 'message': 'No compatible transitions at these widths'})
            continue
        matrix = csr_matrix(np.array(rows, dtype=float))
        bound = np.array(rhs, dtype=float)
        scales = np.maximum(1, abs(matrix).max(axis=0).toarray().ravel())
        scaled = matrix.multiply(1/scales).tocsr()
        result = linprog(np.zeros(pair.DIM) if signed else 1/scales,
                         A_ub=scaled, b_ub=bound,
                         bounds=[(None, None) if signed else (0, None)]*pair.DIM,
                         method='highs', options={'time_limit': 15})
        item = {'inner_width': width, 'lags': [min_lag, max_lag], 'new_pairs': count,
                'new_flips': flips, 'total_pairs': total, 'status': int(result.status),
                'message': result.message, 'candidate_accepted': False}
        if result.success:
            coefficients = result.x/scales
            item.update(coefficients=coefficients.tolist(),
                        max_training_residual=float(np.max(matrix @ coefficients-bound)),
                        holdout=holdout(coefficients, min_lag, max_lag)
                        if min_lag == max_lag else holdout(coefficients))
        report['results'].append(item)
        report['seconds'] = perf_counter()-began
        output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({k: v for k, v in item.items() if k != 'coefficients'}), flush=True)
        if not result.success:
            break
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--width', type=int, default=8)
    parser.add_argument('--lag', type=int, default=10)
    parser.add_argument('--min-lag', type=int, default=2)
    parser.add_argument('--signed', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(args.width, args.lag, args.signed, args.output, args.min_lag)
