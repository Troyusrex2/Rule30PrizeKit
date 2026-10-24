"""Counterexample-guided nonlocal sum-of-squares feature generation.

Every prefix-count square is nonnegative on arbitrary finite rows. A finite
dual may expose a missing square through a negative eigenvector. If a
rational dual has positive reward, nonnegative linear gains, and PSD gains
for every Gram block, it rejects this ENTIRE quadratic prefix-square cone
on the actual finite pairs. Such exact arithmetic is still NOT a Lean proof
and rejects neither the prize statement nor arbitrary nonlocal rankings.
"""

import argparse
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
from time import perf_counter

import numpy as np
from scipy.optimize import linprog
import sympy as sp

import paired_nonlocal_rank_probe as base


def grams(a, b, center):
    cells = base.letters(a, b, center)
    result = np.zeros((5, 4, 4), dtype=np.int64)
    for group in range(4):
        side = (0, 2)[group//2]
        word = [s for p, s in cells if base.region(p) == side]
        if group % 2:
            word.reverse()
        v = np.zeros(4, dtype=np.int64)
        for symbol in word:
            v[symbol] += 1
            result[group] += np.outer(v, v)
    v = np.bincount([s for _, s in cells], minlength=4)
    result[4] = np.outer(v, v)
    return result


def canonical(vector):
    divisor = math.gcd(*vector)
    vector = tuple(v//divisor for v in vector)
    return tuple(-v for v in vector) if next(v for v in vector if v) < 0 else vector


def matrix_for(linear, gram_delta, squares):
    columns = [linear]
    for group, q in squares:
        v = np.array(q, dtype=float)
        columns.append(np.einsum('i,nij,j->n', v, gram_delta[:, group], v)[:, None])
    return np.concatenate(columns, axis=1)


def exact_dual(records, linear, gram_delta, reward, multipliers):
    # One common denominator avoids an enormous LCM of unrelated rounded
    # coordinates. Failure to reconstruct a certificate stays UNKNOWN.
    for denominator in (100, 1000, 10000, 100000, 1000000):
        weights = [int(round(float(q)*denominator)) for q in multipliers]
        result = analyze_dual(records, linear, gram_delta, reward, weights)
        result['common_denominator'] = denominator
        if result['passed']:
            return result
    return result


def analyze_dual(records, linear, gram_delta, reward, weights):
    linear_gain = np.array(weights, dtype=object) @ linear.astype(object)
    gram_gain = sum((w*g.astype(object) for w, g in zip(weights, gram_delta)),
                    np.zeros(gram_delta.shape[1:], dtype=object))
    total_reward = sum(w*int(r) for w, r in zip(weights, reward))
    minors = []
    for group in range(gram_delta.shape[1]):
        values = []
        M = sp.Matrix(gram_gain[group].tolist())
        for size in range(1, 5):
            for indices in itertools.combinations(range(4), size):
                values.append(int(M.extract(indices, indices).det()))
        minors.append(values)
    passed = (all(w >= 0 for w in weights) and min(linear_gain) >= 0
              and total_reward > 0 and all(min(values) >= 0 for values in minors))
    return {'passed': bool(passed), 'combined_reward': int(total_reward),
            'linear_gain_min': int(min(linear_gain)),
            'principal_minors': minors,
            'gram_gains': [[[int(v) for v in row] for row in M] for M in gram_gain],
            'chosen': [dict(multiplier=w, outer=str(record[0]), inner=str(record[1]),
                            center_index=record[2], reward=record[5])
                       for w, record in zip(weights, records) if w]}


def run(max_width, max_rounds, output, restarts=False, max_lag=10):
    began = perf_counter()
    if restarts:
        import restart_nonlocal_rank_probe as restart
        records = []
        for width in range(3, max_width+1):
            for middle in range(1 << (width-2)):
                row = (middle << 1) | 1 | (1 << (width-1))
                for center in range(1, width-1):
                    for lag in range(2, max_lag+1):
                        record = restart.transition(row, center, lag)
                        if record is not None:
                            records.append(record)
    else:
        records = [record for width in range(5, max_width+1) for record in base.cases(width)]
    linear = np.array([r[4][:252]-r[3][:252] for r in records], dtype=np.int64)
    gram_delta = np.array([grams(base.step(r[0]), base.step(r[1]), r[2]+1)-grams(*r[:3])
                           for r in records], dtype=np.int64)
    reward = np.array([r[5] for r in records], dtype=np.int64)
    squares = [(group, tuple(q)) for group in range(5) for q in base.CHARGES]
    # Exact Gram accounting agrees with the independently checked original
    # prefix-square features, on every actual training transition.
    first_matrix = matrix_for(linear, gram_delta, squares)
    original = np.array([r[4]-r[3] for r in records], dtype=np.int64)
    assert np.array_equal(first_matrix, original)
    report = {'Lean_verified': False, 'full_problem_solved': False,
              'FlipRanking_proved': False, 'scope': 'Actual pairs and nonnegative ordered-pair counts plus arbitrary PSD prefix-count quadratics',
              'max_initial_width': max_width, 'actual_pairs': len(records),
              'exact_restart_relation': restarts, 'max_lag': max_lag if restarts else None,
              'gram_feature_controls_passed': True, 'rounds': [],
              'candidate_accepted': False, 'all_squares_refuted_by_exact_dual': False}
    for iteration in range(max_rounds):
        A = matrix_for(linear, gram_delta, squares)
        scales = np.maximum(1, np.max(np.abs(A), axis=0))
        scaled_A = A/scales
        objective = np.ones(A.shape[1])
        for j, (_, q) in enumerate(squares):
            objective[252+j] = sum(v*v for v in q)
        fit = linprog(objective/scales, A_ub=scaled_A, b_ub=-reward,
                      bounds=[(0, None)]*A.shape[1], method='highs', options={'time_limit': 15})
        item = {'iteration': iteration, 'square_features': len(squares),
                'status': int(fit.status), 'message': fit.message}
        if fit.success:
            coefficients = fit.x/scales
            item['max_training_residual'] = float(np.max(A @ coefficients+reward))
            item['coefficients'] = coefficients.tolist()
            report['finite_candidate'] = {'squares': squares, 'coefficients': coefficients.tolist(),
                                          'actual_training_pairs': len(records)}
            report['rounds'].append(item)
            break
        if fit.status != 2:
            report['rounds'].append(item)
            break
        dual = linprog(np.ones(len(records)), A_ub=-scaled_A.T, b_ub=np.zeros(A.shape[1]),
                       A_eq=[reward], b_eq=[1], bounds=[(0, None)]*len(records),
                       method='highs', options={'time_limit': 15})
        item['dual_status'] = int(dual.status)
        if not dual.success:
            report['rounds'].append(item)
            break
        gains = np.einsum('n,ngij->gij', dual.x, gram_delta)
        added = []
        for group in range(5):
            values, vectors = np.linalg.eigh(gains[group])
            if values[0] >= -1e-8:
                continue
            direction = vectors[:, 0]
            for scale in (2, 4, 8, 16, 32, 64, 128, 256):
                q = tuple(int(v) for v in np.rint(scale*direction))
                if not any(q):
                    continue
                q = canonical(q)
                if (group, q) in squares:
                    continue
                value = float(np.array(q) @ gains[group] @ np.array(q))
                if value < -1e-8:
                    squares.append((group, q))
                    added.append({'group': group, 'charge': q, 'dual_gain': value})
                    break
        item['added_squares'] = added
        if not added:
            certificate = exact_dual(records, linear, gram_delta, reward, dual.x)
            report['exact_dual'] = certificate
            report['all_squares_refuted_by_exact_dual'] = certificate['passed']
            report['rounds'].append(item)
            break
        report['rounds'].append(item)
        report['seconds'] = perf_counter()-began
        output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
        if iteration % 8 == 0:
            print(json.dumps(item), flush=True)
    report['seconds'] = perf_counter()-began
    output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'rounds': len(report['rounds']), 'finite_candidate': 'finite_candidate' in report,
                      'exact_PSD_dual_passed': report['all_squares_refuted_by_exact_dual'],
                      'seconds': report['seconds']}), flush=True)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--width', type=int, default=6)
    parser.add_argument('--rounds', type=int, default=64)
    parser.add_argument('--restarts', action='store_true')
    parser.add_argument('--lag', type=int, default=10)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(args.width, args.rounds, args.output, args.restarts, args.lag)
