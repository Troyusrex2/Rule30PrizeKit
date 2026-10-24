"""Falsify a nonnegative max-prefix/gap rank for the full nested-pair target.

The spatial word includes white gaps inside the outer support edges. Every
feature is a nonnegative maximum of integer sums, so a nonnegative rational
combination could give a natural-valued rank after scaling. Fitting finitely
many transitions does not prove all-length descent or Problem 1.
"""

import argparse
from fractions import Fraction
from itertools import product
import json
from math import lcm
from pathlib import Path
import random
from time import perf_counter

import numpy as np
from scipy.linalg import qr
from scipy.optimize import linprog
from sympy import Matrix

import paired_nonlocal_rank_probe as pair
from restart_nonlocal_rank_probe import restart_pair
from validate_restart_rank_structured import alternating_start


CHARGES = np.array([v for v in product((-1, 0, 1), repeat=4) if max(v)>0], dtype=np.int64)
BASE_DIM = 6*len(CHARGES)+1
DIM = 2*BASE_DIM


def features(a, b, center, brute=False):
    assert pair.nested(a, b, center)
    out = []
    for indices in (range(center), range(center+1, a.bit_length())):
        word = [((a >> i) & 1)+2*((b >> i) & 1) for i in indices]
        if brute:
            values = []
            for charge in CHARGES:
                sums = [sum(int(charge[s]) for s in word[:j]) for j in range(len(word)+1)]
                values.append((max(sums), max(sums[-1]-v for v in sums),
                    max(sums[j]-sums[i] for j in range(len(sums)) for i in range(j+1))))
            out.extend(np.array(values, dtype=np.int64).T.ravel())
        else:
            sums = np.concatenate((np.zeros((len(CHARGES), 1), dtype=np.int64),
                np.cumsum(CHARGES[:, word], axis=1)), axis=1)
            out.extend(np.max(sums, axis=1))
            out.extend(sums[:, -1]-np.min(sums, axis=1))
            out.extend(np.max(sums-np.minimum.accumulate(sums, axis=1), axis=1))
    out.append(1)
    value = np.zeros(DIM, dtype=np.int64)
    mode = (a >> center) & 1
    value[mode*BASE_DIM:(mode+1)*BASE_DIM] = out
    assert value.min() >= 0
    return value


def compatible(a, b, center):
    return (pair.nested(a, b, center) and (a >> center) & 1 == (b >> center) & 1
        and (pair.step(a) >> (center+1)) & 1 == (pair.step(b) >> (center+1)) & 1)


def record(a, b, center):
    assert compatible(a, b, center)
    na, nb = pair.step(a), pair.step(b)
    reward = int(((a >> center) & 1) != ((na >> (center+1)) & 1))
    return features(na, nb, center+1)-features(a, b, center), reward


def controls():
    rng = random.Random(202610241138)
    for _ in range(40):
        width = rng.randrange(5, 19)
        c = rng.randrange(2, width-2)
        a = rng.getrandbits(width) | 1 | (1 << (width-1))
        b = (rng.getrandbits(width-2) << 1) | (1 << (c-1)) | (1 << (c+1))
        assert np.array_equal(features(a, b, c), features(a, b, c, brute=True))
        for row in (a, b):
            cells = {i-c for i in range(width) if row >> i & 1}
            nxt = {p for p in range(-c-1, width-c+1)
                   if (p-1 in cells) ^ ((p in cells) or (p+1 in cells))}
            assert pair.step(row) == sum(1 << (p+c+1) for p in nxt)
    return {'maxima_vs_direct_subarray_checks': 40,
            'packed_vs_cellwise_evolutions': 80, 'AllPassed': True}


def training_cases():
    cases = set()

    def add(a, b, c):
        if compatible(a, b, c):
            cases.add((a, b, c))

    for width in range(5, 8):
        for outer in range(1 << (width-2)):
            a = (outer << 1) | 1 | (1 << (width-1))
            for inner in range(1 << (width-2)):
                for c in range(2, width-2):
                    add(a, inner << 1, c)
    rng = random.Random(202610241139)
    accepted = 0
    while accepted < 1024:
        w = rng.randrange(5, 65)
        c = rng.randrange(2, w-2)
        a = rng.getrandbits(w) | 1 | (1 << (w-1))
        b = rng.getrandbits(w-2) << 1
        if compatible(a, b, c):
            cases.add((a, b, c))
            accepted += 1
    row = 1
    for t in range(160):
        for lag in (2, 3, 4, 8, 16):
            add(*restart_pair(row, t, lag))
        row = pair.step(row)
    for n in (8, 16, 32, 64, 128, 256):
        a, b, c = 1 | (7 << (n-1)) | (1 << (2*n)), 7 << (n-1), n
        for t in range(min(n-2, 64)):
            add(a, b, c)
            a, b, c = pair.step(a), pair.step(b), c+1
    for n in (32, 64, 128):
        for right in (0, 3):
            row, c = alternating_start(n, right)
            for t in range(n+1):
                assert (row >> c) & 1 == int(t % 2 == 0)
                if 1 <= t <= 16:
                    add(*restart_pair(row, c, 2))
                row, c = pair.step(row), c+1
    return sorted(cases)


def is_restart(case):
    a, b, c = case
    lag = (b & -b).bit_length()-1
    if lag < 2:
        return False
    row = b >> lag
    return a.bit_length() == row.bit_length()+2*lag and restart_pair(row, c-lag, lag) == case


def restricted_cases(domain):
    cases = set()
    row = 1
    for t in range(256):
        for lag in (2, 3, 4, 8, 16, 32):
            case = restart_pair(row, t, lag)
            if compatible(*case):
                cases.add(case)
        row = pair.step(row)
    if domain == 'restart':
        cases.update(c for c in training_cases() if is_restart(c))
        rng = random.Random(202610241143)
        accepted = 0
        while accepted < 1024:
            width = rng.randrange(3, 65)
            c = rng.randrange(1, width-1)
            row = rng.getrandbits(width) | 1 | (1 << (width-1))
            case = restart_pair(row, c, rng.randrange(2, 33))
            if compatible(*case):
                cases.add(case)
                accepted += 1
    assert all(is_restart(c) for c in cases)
    return sorted(cases)


def holdout_cases(domain):
    if domain == 'seed':
        row = 1
        for t in range(1024):
            if t >= 256:
                for lag in (2, 3, 4, 8, 16, 32, 64, 128):
                    case = restart_pair(row, t, lag)
                    if compatible(*case):
                        yield case, {'seed_time': t, 'lag': lag}
            row = pair.step(row)
    else:
        for n in (256, 512):
            for right in (5, 17, 255):
                row, c = alternating_start(n, right)
                for t in range(n+1):
                    assert (row >> c) & 1 == int(t % 2 == 0)
                    if 1 <= t <= 64:
                        yield restart_pair(row, c, 2), {'construction': n,
                            'right_initial': right, 'time': t, 'lag': 2}
                    row, c = pair.step(row), c+1


def exact_dual(matrix, rewards, cases):
    dual = linprog(np.ones(len(cases)), A_ub=-matrix.T, b_ub=np.zeros(DIM),
                   A_eq=rewards.reshape(1, -1), b_eq=[1], bounds=(0, None),
                   method='highs', options={'time_limit': 15})
    out = {'solver_status': int(dual.status), 'exact_certificate_passed': False}
    if not dual.success:
        return out
    support = np.flatnonzero(dual.x > 1e-9)
    gains_float = matrix.T@dual.x
    tight = np.flatnonzero(abs(gains_float) < 1e-7)
    equations = np.concatenate((rewards[support].reshape(1, -1),
                               matrix[np.ix_(support, tight)].T), axis=0)
    rhs = np.zeros(len(equations), dtype=np.int64)
    rhs[0] = 1
    _, triangular, pivot = qr(equations.T.astype(float), pivoting=True, mode='economic')
    rank = int(np.sum(abs(np.diag(triangular)) > 1e-8))
    out.update(supported_cases=len(support), active_equation_rank=rank)
    if rank != len(support):
        return out
    selected = pivot[:len(support)]
    try:
        exact = Matrix(equations[selected].tolist()).inv(method='DM')*Matrix(rhs[selected].tolist())
    except ValueError:
        return out
    weights = [(int(i), Fraction(int(v.p), int(v.q))) for i, v in zip(support, exact)]
    scale = lcm(*(f.denominator for _, f in weights))
    integers = [(i, int(f*scale)) for i, f in weights]
    gains = [sum(v*int(matrix[i, j]) for i, v in integers) for j in range(DIM)]
    reward = sum(v*int(rewards[i]) for i, v in integers)
    passed = all(v>=0 for _, v in integers) and min(gains)>=0 and reward>0
    out.update(exact_certificate_passed=passed, supported_cases=len(integers),
               weighted_reward=str(reward), minimum_gain=str(min(gains)))
    if passed:
        out['terms'] = [dict(outer=str(cases[i][0]), inner=str(cases[i][1]),
            center=cases[i][2], multiplier=str(v)) for i, v in integers]
        out['gains'] = list(map(str, gains))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--domain', choices=('nested', 'restart', 'seed'), default='nested')
    args = parser.parse_args()
    began = perf_counter()
    report = {'Lean_verified': False, 'full_problem_solved': False,
              'FlipRanking_proved': False, 'candidate_accepted': False,
              'features': DIM, 'charge_directions': len(CHARGES), 'controls': controls(),
              'transition_domain': args.domain}
    cases = training_cases() if args.domain == 'nested' else restricted_cases(args.domain)
    matrix, rewards = zip(*(record(*c) for c in cases))
    matrix, rewards = np.array(matrix), np.array(rewards)
    scales = np.maximum(1, abs(matrix).max(axis=0))
    fit = linprog(1/scales, A_ub=matrix/scales, b_ub=-rewards, bounds=(0, None),
                  method='highs', options={'time_limit': 15})
    report.update(training_cases=len(cases), color_changes=int(sum(rewards)),
                  solver_status=int(fit.status), solver_message=fit.message)
    if fit.success:
        coefficients = fit.x/scales
        report['coefficients'] = coefficients.tolist()
        report['max_training_residual'] = float(np.max(matrix@coefficients+rewards))
        failures, tested = [], 0
        for case, provenance in holdout_cases(args.domain):
            delta, reward = record(*case)
            residual = float(delta@coefficients+reward)
            tested += 1
            if residual > 1e-7:
                a, b, c = case
                failures.append(dict(outer=str(a), inner=str(b), center=c,
                                     residual=residual, **provenance))
        report['independent_holdout'] = {'tested_cases': tested,
            'failures': len(failures), 'first_failure': failures[0] if failures else None}
    elif fit.status == 2:
        report['dual'] = exact_dual(matrix, rewards, cases)
    report['seconds'] = perf_counter()-began
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('coefficients','dual')}), flush=True)
    if 'dual' in report:
        print(json.dumps({k:v for k,v in report['dual'].items() if k not in ('terms','gains')}), flush=True)


if __name__ == '__main__':
    main()
