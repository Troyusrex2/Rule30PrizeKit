"""Directional global/radial Gram potentials on exact restart pairs.

Regional count differences are not represented by separate left/right
prefix squares. This discovery model retains nonnegativity through PSD
forms, but every fitted descent inequality remains finite and untrusted.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
import json
from pathlib import Path
import random
from time import perf_counter

import clarabel
import numpy as np
from scipy import sparse

import paired_nonlocal_rank_probe as pair
from paired_prefix_sos_probe import grams
import restart_nonlocal_rank_probe as restart
from restart_prefix_sdp import conic_control, records_at_widths
from seed_nonlocal_sdp_probe import seed_rows, record as seed_record


@lru_cache(maxsize=16384)
def blocks(a, b, center, radial=False):
    out = [M for M in grams(a, b, center)[:4]]
    cells = pair.letters(a, b, center)
    v = np.zeros(12, dtype=np.int64)
    for p, symbol in cells:
        v[4*pair.region(p)+symbol] += 1
    out.append(np.outer(v, v))
    if radial:
        sides = [[s for p, s in cells if p < 0][::-1], [s for p, s in cells if p > 0]]
        v = np.zeros(8, dtype=np.int64)
        M = np.zeros((8, 8), dtype=np.int64)
        for depth in range(max(map(len, sides))):
            for side in (0, 1):
                if depth < len(sides[side]):
                    v[4*side+sides[side][depth]] += 1
            M += np.outer(v, v)
        out.append(M)
    return out


def exact_psd(matrix):
    """Exact rational Schur elimination; singular PSD matrices are allowed."""
    A = [[Fraction(int(v)) for v in row] for row in matrix]
    assert all(A[i][j] == A[j][i] for i in range(len(A)) for j in range(len(A)))
    pivots = []
    while A:
        if any(A[i][i] < 0 for i in range(len(A))):
            return {'passed': False, 'pivots': list(map(str, pivots)), 'reason': 'negative diagonal'}
        positive = next((i for i in range(len(A)) if A[i][i] > 0), None)
        if positive is None:
            return {'passed': all(v == 0 for row in A for v in row),
                    'pivots': list(map(str, pivots)), 'reason': 'zero diagonal residual'}
        order = [positive]+[i for i in range(len(A)) if i != positive]
        A = [[A[i][j] for j in order] for i in order]
        pivot = A[0][0]
        pivots.append(pivot)
        A = [[A[i][j]-A[i][0]*A[0][j]/pivot for j in range(1, len(A))]
             for i in range(1, len(A))]
    return {'passed': True, 'pivots': list(map(str, pivots)), 'reason': 'positive Schur pivots'}


def controls(radial):
    assert exact_psd([[1, 1], [1, 1]])['passed']
    assert exact_psd([[0, 0], [0, 1]])['passed']
    assert not exact_psd([[0, 1], [1, 0]])['passed']
    rng = random.Random(202610240941)
    for _ in range(32):
        width = rng.randrange(5, 30)
        center = rng.randrange(2, width-2)
        a = rng.getrandbits(width) | 1 | (1 << (width-1))
        b = rng.getrandbits(width-2) << 1
        matrices = blocks(a, b, center, radial)
        cells = pair.letters(a, b, center)
        q = [rng.randrange(-3, 4) for _ in range(12)]
        total = sum(q[4*pair.region(p)+s] for p, s in cells)
        assert int(np.array(q) @ matrices[4] @ np.array(q)) == total*total
        if radial:
            sides = [[s for p, s in cells if p < 0][::-1], [s for p, s in cells if p > 0]]
            q = [rng.randrange(-3, 4) for _ in range(8)]
            total = expected = 0
            for d in range(max(map(len, sides))):
                for side in (0, 1):
                    if d < len(sides[side]):
                        total += q[4*side+sides[side][d]]
                expected += total*total
            assert int(np.array(q) @ matrices[5] @ np.array(q)) == expected
    return {'Schur_PSD_controls': 3, 'direct_regional_square_controls': 32,
            'direct_radial_square_controls': 32 if radial else 0, 'AllPassed': True}


def features(record, radial, runs, updated=False):
    a, b, center, old, new, reward = record
    if updated:
        a, b, center, moments = pair.step(a), pair.step(b), center+1, new
    else:
        moments = old
    linear = moments[:252]
    if runs:
        from restart_run_rank_probe import run_features
        linear = np.r_[linear, run_features(a, b, center)]
    return (a >> center) & 1, linear, blocks(a, b, center, radial)


def fit(records, seconds, radial, runs, reduce_linear=False):
    base_linear = 588 if runs else 252
    linear_dim = 2*base_linear
    sizes = [4, 4, 4, 4, 12]+([8] if radial else [])
    sizes *= 2
    triangles = [[(i, j) for j in range(n) for i in range(j+1)] for n in sizes]
    L = np.zeros((len(records), linear_dim), dtype=np.int64)
    G = [np.zeros((len(records), n, n), dtype=np.int64) for n in sizes]
    group_count = len(sizes)//2
    for k, record in enumerate(records):
        for updated, sign in ((False, -1), (True, 1)):
            mode, linear, matrices = features(record, radial, runs, updated)
            L[k, mode*base_linear:(mode+1)*base_linear] += sign*linear
            for j, matrix in enumerate(matrices):
                G[mode*group_count+j][k] += sign*matrix
    full_L = L
    full_linear_dim = linear_dim
    representatives = list(range(linear_dim))
    if reduce_linear:
        signatures = {}
        representatives = []
        for j in range(linear_dim):
            divisor = int(np.gcd.reduce(abs(L[:, j])))
            if not divisor:
                continue
            signature = (L[:, j]//divisor).tobytes()
            if signature not in signatures:
                signatures[signature] = j
                representatives.append(j)
        assert representatives
        L = L[:, representatives]
        linear_dim = len(representatives)
    offsets = [linear_dim]
    for triangle in triangles:
        offsets.append(offsets[-1]+len(triangle))
    dim = offsets[-1]
    reward = np.array([r[5] for r in records], dtype=float)
    ls = np.maximum(1, np.max(abs(L), axis=0))
    gs = [max(1, np.max(abs(g))) for g in G]
    descent = np.zeros((len(records), dim))
    descent[:, :linear_dim] = L/ls
    for group, triangle in enumerate(triangles):
        for j, (a, b) in enumerate(triangle):
            descent[:, offsets[group]+j] = G[group][:, a, b]*(1 if a == b else 2)/gs[group]
    positive = sparse.hstack([-sparse.eye(linear_dim), sparse.csc_matrix((linear_dim, dim-linear_dim))])
    semidefinite = np.zeros((dim-linear_dim, dim))
    q = np.r_[np.ones(linear_dim), np.zeros(dim-linear_dim)]
    for group, triangle in enumerate(triangles):
        for j, (a, b) in enumerate(triangle):
            semidefinite[offsets[group]-linear_dim+j, offsets[group]+j] = -1 if a == b else -2**.5
            if a == b:
                q[offsets[group]+j] = 1
    A = sparse.vstack([sparse.csc_matrix(descent), positive, sparse.csc_matrix(semidefinite)]).tocsc()
    b = np.r_[-reward, np.zeros(dim)]
    cones = [clarabel.NonnegativeConeT(len(records)+linear_dim)]+[clarabel.PSDTriangleConeT(n) for n in sizes]
    settings = clarabel.DefaultSettings()
    settings.verbose = False
    settings.time_limit = float(seconds)
    settings.max_iter = 300
    solution = clarabel.DefaultSolver(sparse.csc_matrix((dim, dim)), q, A, b, cones, settings).solve()
    result = {'status': str(solution.status), 'actual_training_pairs': len(records),
              'variables': dim, 'radial': radial, 'run_features': runs,
              'full_linear_features': full_linear_dim, 'retained_linear_columns': linear_dim,
              'exact_positive_multiple_column_reduction': reduce_linear,
              'solve_time': solution.solve_time, 'candidate_accepted': False}
    if str(solution.status) in ('Solved', 'AlmostSolved'):
        x = np.array(solution.x)
        weights = np.zeros(full_linear_dim)
        weights[representatives] = x[:linear_dim]/ls
        matrices = [np.zeros((n, n)) for n in sizes]
        for group, triangle in enumerate(triangles):
            for j, (a, b) in enumerate(triangle):
                matrices[group][a, b] = matrices[group][b, a] = x[offsets[group]+j]/gs[group]
        residual = full_L @ weights+sum(np.einsum('ij,nij->n', M, g) for M, g in zip(matrices, G))+reward
        assert max(abs(residual-(descent @ x+reward))) < 1e-4
        result.update(coefficients=weights.tolist(), matrices=[M.tolist() for M in matrices],
                      max_training_residual=float(residual.max()),
                      minimum_linear_coefficient=float(weights.min()),
                      minimum_Gram_eigenvalues=[float(np.linalg.eigvalsh(M)[0]) for M in matrices])
    elif str(solution.status) in ('PrimalInfeasible', 'AlmostPrimalInfeasible'):
        multipliers = np.array(solution.z[:len(records)])
        total = float(multipliers @ reward)
        attempts = []
        if total > 1e-12:
            multipliers /= total
            for denominator in (100, 1000, 10000, 100000, 1000000):
                weights = np.array([round(float(v)*denominator) for v in multipliers], dtype=object)
                gain = weights @ full_L.astype(object)
                matrices = [sum((w*m.astype(object) for w, m in zip(weights, g)),
                                np.zeros(g.shape[1:], dtype=object)) for g in G]
                psd = [exact_psd(M) for M in matrices]
                charge = sum(int(w)*r[5] for w, r in zip(weights, records))
                passed = min(weights) >= 0 and min(gain) >= 0 and charge > 0 and all(p['passed'] for p in psd)
                attempt = {'common_denominator': denominator, 'passed': bool(passed),
                           'minimum_linear_gain': int(min(gain)), 'combined_reward': int(charge),
                           'PSD_checks': psd}
                attempts.append(attempt)
                if passed:
                    attempt['chosen'] = [dict(multiplier=int(w), outer=str(r[0]), inner=str(r[1]),
                                              center_index=r[2], reward=r[5])
                                         for w, r in zip(weights, records) if w]
                    attempt['Gram_gains'] = [[[int(v) for v in row] for row in M] for M in matrices]
                    break
        result['exact_dual_attempts'] = attempts
        result['exact_dual_passed'] = any(a['passed'] for a in attempts)
        result['floating_infeasibility_is_not_a_proof'] = True
    return result


def score(record, result, updated):
    mode, linear, matrices = features(record, result['radial'], result['run_features'], updated)
    base_linear = len(linear)
    count = len(matrices)
    weights = np.array(result['coefficients'][mode*base_linear:(mode+1)*base_linear])
    Q = [np.array(M) for M in result['matrices'][mode*count:(mode+1)*count]]
    return float(linear @ weights+sum(np.einsum('ij,ij->', q, g) for q, g in zip(Q, matrices)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', action='store_true')
    parser.add_argument('--time', type=int, default=640)
    parser.add_argument('--width', type=int, default=8)
    parser.add_argument('--min-lag', type=int, default=2)
    parser.add_argument('--lag', type=int, default=2)
    parser.add_argument('--seconds', type=int, default=20)
    parser.add_argument('--radial', action='store_true')
    parser.add_argument('--runs', action='store_true')
    parser.add_argument('--cegar-rounds', type=int, default=1)
    parser.add_argument('--reduce-linear', action='store_true')
    parser.add_argument('--resume', type=Path)
    parser.add_argument('--structured', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    began = perf_counter()
    validation = []
    if args.seed:
        rows = seed_rows(args.time+args.lag+514)
        records = [r for t in range(1, args.time+1) for lag in range(args.min_lag, args.lag+1)
                   if (r := seed_record(rows, t, lag)) is not None]
        for t in range(args.time+1, args.time+513):
            for lag in range(args.min_lag, args.lag+1):
                rec = seed_record(rows, t, lag)
                if rec is not None:
                    validation.append((rec, {'seed_time': t, 'lag': lag,
                                             'batch': int(t > args.time+256)}))
    else:
        records = records_at_widths(args.width, args.min_lag, args.lag)
        rng = random.Random(202610240948)
        for _ in range(50000):
            width = rng.randrange(3, 65)
            center = rng.randrange(1, width-1)
            lag = rng.randrange(args.min_lag, (args.lag if args.min_lag == args.lag else 64)+1)
            row = rng.getrandbits(width) | 1 | (1 << (width-1))
            rec = restart.transition(row, center, lag)
            if rec is not None:
                validation.append((rec, {'row': str(row), 'center': center, 'lag': lag,
                                         'width': width, 'batch': len(validation)//512}))
            if len(validation) == 1024:
                break
        assert len(validation) == 1024
    existing = {(r[0], r[1], r[2]) for r in records}
    resumed = 0
    if args.resume:
        prior = json.loads(args.resume.read_text(encoding='utf-8'))
        for step in prior['iterations']:
            for counter in step.get('added_actual_counterexamples', []):
                if 'row' in counter:
                    rec = restart.transition(int(counter['row']), counter['center'], counter['lag'])
                else:
                    raise ValueError('This resume path currently expects general finite-row counterexamples')
                assert rec is not None
                key = rec[:3]
                if key not in existing:
                    existing.add(key)
                    records.append(rec)
                    resumed += 1
        assert len(records) >= prior['result']['actual_training_pairs']
    structured = 0
    if args.structured:
        assert args.min_lag == args.lag == 2
        from validate_restart_rank_structured import alternating_start
        for length in (16, 32, 64, 128, 256):
            row, center = alternating_start(length)
            for t in range(1, min(length-2, 33)):
                row, center = pair.step(row), center+1
                rec = restart.transition(row, center, 2)
                assert rec is not None and rec[5] == 1
                key = rec[:3]
                if key not in existing:
                    existing.add(key)
                    records.append(rec)
                    structured += 1
    report = {'Lean_verified': False, 'full_problem_solved': False, 'rank_proved': False,
              'single_seed_only': args.seed, 'max_seed_time': args.time if args.seed else None,
              'inner_width': None if args.seed else args.width,
              'lags': [args.min_lag, args.lag], 'conic_controls': conic_control(),
              'feature_controls': controls(args.radial), 'iterations': [],
              'resumed_actual_pairs': resumed, 'structured_actual_pairs': structured,
              'solver_version': clarabel.__version__}
    seen = {(r[0], r[1], r[2]) for r in records}
    for iteration in range(args.cegar_rounds):
        result = fit(records, args.seconds, args.radial, args.runs, args.reduce_linear)
        counters = []
        if 'coefficients' in result:
            counts = [0, 0]
            failures = [0, 0]
            negative = 0
            for rec, metadata in validation:
                old, new = score(rec, result, False), score(rec, result, True)
                residual = new-old+rec[5]
                batch = metadata['batch']
                counts[batch] += 1
                negative += int(min(old, new) < -1e-5)
                if residual > 1e-5:
                    failures[batch] += 1
                    counters.append((residual, rec, dict(metadata, residual=residual, reward=rec[5])))
            counters.sort(key=lambda x: x[0], reverse=True)
            result['holdout'] = {'actual_pairs_by_batch': counts, 'descent_failures_by_batch': failures,
                                 'negative_values': negative,
                                 'worst': counters[0][2] if counters else None}
        report['iterations'].append(result)
        report['result'] = result
        report['seconds'] = perf_counter()-began
        args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({'iteration': iteration, **{k: v for k, v in result.items()
              if k not in ('coefficients', 'matrices', 'exact_dual_attempts')}}), flush=True)
        if not counters:
            break
        added = []
        for residual, rec, metadata in counters[:64]:
            key = (rec[0], rec[1], rec[2])
            if key not in seen:
                seen.add(key)
                records.append(rec)
                added.append(metadata)
        result['added_actual_counterexamples'] = added
        if not added:
            report['stopped_reason'] = 'Repeated numerical training counterexample'
            break
    report['seconds'] = perf_counter()-began
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n', encoding='utf-8', newline='\n')
