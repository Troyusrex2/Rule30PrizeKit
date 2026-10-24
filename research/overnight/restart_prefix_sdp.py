"""Finite SDP discovery for nonlocal ranks on exact Rule-30 restart pairs.

The rank cone has nonnegative ordered-pair counts and arbitrary PSD
quadratic forms in regional prefix counts. Solver output is untrusted:
all-length descent and rational/kernel verification are still required.
Uses isolated Clarabel; no system Python packages are modified.
"""

import argparse
import json
from pathlib import Path
import random
from time import perf_counter

import clarabel
import numpy as np
from scipy import sparse

import paired_nonlocal_rank_probe as pair
from paired_prefix_sos_probe import grams, exact_dual
import restart_nonlocal_rank_probe as restart


TRIANGLE = [(i, j) for j in range(4) for i in range(j+1)]
DIM = 252+5*10


def conic_control():
    P = sparse.csc_matrix((3, 3))
    q = np.array([1., 0., 1.])
    A = sparse.vstack([sparse.csc_matrix([[0., 1., 0.]]),
                       -sparse.diags([1., 2**.5, 1.])]).tocsc()
    settings = clarabel.DefaultSettings()
    settings.verbose = False
    settings.time_limit = 10.
    result = clarabel.DefaultSolver(P, q, A, np.array([1., 0., 0., 0.]),
             [clarabel.ZeroConeT(1), clarabel.PSDTriangleConeT(2)], settings).solve()
    assert str(result.status) == 'Solved'
    assert abs(result.obj_val-2) < 1e-6 and max(abs(x-1) for x in result.x) < 1e-6
    return {'known_trace_minimum_two': True, 'off_diagonal_sqrt_two_scaling': True}


def records_at_widths(max_width, min_lag, max_lag):
    records = []
    for width in range(3, max_width+1):
        for middle in range(1 << (width-2)):
            row = (middle << 1) | 1 | (1 << (width-1))
            for center in range(1, width-1):
                for lag in range(min_lag, max_lag+1):
                    record = restart.transition(row, center, lag)
                    if record is not None:
                        records.append(record)
    return records


def fit(records, seconds, color=False):
    modes = 2 if color else 1
    linear_dim = 252*modes
    groups = 5*modes
    dim = linear_dim+10*groups
    linear = np.zeros((len(records), linear_dim), dtype=np.int64)
    G = np.zeros((len(records), groups, 4, 4), dtype=np.int64)
    for n, r in enumerate(records):
        old_mode = ((r[0] >> r[2]) & 1) if color else 0
        new_mode = ((pair.step(r[0]) >> (r[2]+1)) & 1) if color else 0
        linear[n, old_mode*252:(old_mode+1)*252] -= r[3][:252]
        linear[n, new_mode*252:(new_mode+1)*252] += r[4][:252]
        G[n, old_mode*5:(old_mode+1)*5] -= grams(*r[:3])
        G[n, new_mode*5:(new_mode+1)*5] += grams(pair.step(r[0]), pair.step(r[1]), r[2]+1)
    reward = np.array([r[5] for r in records], dtype=float)
    linear_scale = np.maximum(1, np.max(abs(linear), axis=0))
    gram_scale = np.maximum(1, np.max(abs(G), axis=(0, 2, 3)))
    descent = np.zeros((len(records), dim))
    descent[:, :linear_dim] = linear/linear_scale
    for group in range(groups):
        for index, (i, j) in enumerate(TRIANGLE):
            descent[:, linear_dim+10*group+index] = G[:, group, i, j]*(1 if i == j else 2)/gram_scale[group]
    positive = sparse.hstack([-sparse.eye(linear_dim), sparse.csc_matrix((linear_dim, groups*10))])
    psd_rows = np.zeros((groups*10, dim))
    for group in range(groups):
        for index, (i, j) in enumerate(TRIANGLE):
            psd_rows[10*group+index, linear_dim+10*group+index] = -1 if i == j else -2**.5
    A = sparse.vstack([sparse.csc_matrix(descent), positive, sparse.csc_matrix(psd_rows)]).tocsc()
    b = np.r_[-reward, np.zeros(dim)]
    cones = [clarabel.NonnegativeConeT(len(records)+linear_dim)]+[clarabel.PSDTriangleConeT(4) for _ in range(groups)]
    objective = np.r_[np.ones(linear_dim), np.zeros(groups*10)]
    for group in range(groups):
        for index, (i, j) in enumerate(TRIANGLE):
            if i == j:
                objective[linear_dim+10*group+index] = 1
    settings = clarabel.DefaultSettings()
    settings.verbose = False
    settings.time_limit = float(seconds)
    settings.max_iter = 300
    result = clarabel.DefaultSolver(sparse.csc_matrix((dim, dim)), objective, A, b, cones, settings).solve()
    report = {'status': str(result.status), 'solve_time': result.solve_time,
              'iterations': result.iterations,
              'objective': float(result.obj_val) if np.isfinite(result.obj_val) else None,
              'actual_training_pairs': len(records), 'candidate_accepted': False,
              'color_dependent_weights': color, 'variables': dim}
    if str(result.status) in ('Solved', 'AlmostSolved'):
        x = np.array(result.x)
        weights = x[:linear_dim]/linear_scale
        Q = np.zeros((groups, 4, 4))
        for group in range(groups):
            for index, (i, j) in enumerate(TRIANGLE):
                Q[group, i, j] = Q[group, j, i] = x[linear_dim+10*group+index]/gram_scale[group]
        residual = linear @ weights+np.einsum('gij,ngij->n', Q, G)+reward
        assert np.max(abs(residual-(descent @ x+reward))) < 1e-5
        report.update(linear_coefficients=weights.tolist(), gram_matrices=Q.tolist(),
                      minimum_linear_coefficient=float(weights.min()),
                      gram_minimum_eigenvalues=[float(np.linalg.eigvalsh(M)[0]) for M in Q],
                      max_training_residual=float(residual.max()))
    elif str(result.status) in ('PrimalInfeasible', 'AlmostPrimalInfeasible'):
        multipliers = np.array(result.z[:len(records)])
        total = float(multipliers @ reward)
        if total > 1e-12:
            multipliers /= total
            report['rational_dual_attempt'] = exact_dual(records, linear, G, reward, multipliers)
        report['floating_infeasibility_is_not_a_proof'] = True
    return report


def score(record, coefficients, matrices, updated=False):
    a, b, center, old, new, reward = record
    if updated:
        a, b, center, f = pair.step(a), pair.step(b), center+1, new
    else:
        f = old
    mode = ((a >> center) & 1) if len(coefficients) == 504 else 0
    return float(f[:252] @ coefficients[mode*252:(mode+1)*252]+
                 np.einsum('gij,gij->', matrices[mode*5:(mode+1)*5], grams(a, b, center)))


def holdout(fit_report, min_lag, max_lag):
    weights = np.array(fit_report['linear_coefficients'])
    Q = np.array(fit_report['gram_matrices'])
    rng = random.Random(202610240927)
    accepted = failed = negative = 0
    worst = None
    for _ in range(20000):
        width = rng.randrange(3, 61)
        center = rng.randrange(1, width-1)
        lag = rng.randrange(min_lag, max_lag+1)
        row = rng.getrandbits(width) | 1 | (1 << (width-1))
        record = restart.transition(row, center, lag)
        if record is None:
            continue
        old = score(record, weights, Q)
        new = score(record, weights, Q, True)
        residual = new-old+record[5]
        accepted += 1
        negative += int(min(old, new) < -1e-6)
        if residual > 1e-6:
            failed += 1
            if worst is None or residual > worst['residual']:
                worst = {'row': str(row), 'center': center, 'lag': lag, 'width': width,
                         'residual': residual, 'reward': record[5],
                         'old_score': old, 'new_score': new}
        if accepted == 1024:
            break
    assert accepted == 1024
    return {'actual_restart_transitions': accepted, 'descent_failures': failed,
            'negative_values': negative, 'tested_lags': [min_lag, max_lag], 'worst': worst}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--width', type=int, default=5)
    parser.add_argument('--min-lag', type=int, default=2)
    parser.add_argument('--lag', type=int, default=10)
    parser.add_argument('--seconds', type=int, default=20)
    parser.add_argument('--cegar-rounds', type=int, default=1)
    parser.add_argument('--color', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    began = perf_counter()
    data = records_at_widths(args.width, args.min_lag, args.lag)
    report = {'Lean_verified': False, 'full_problem_solved': False, 'rank_proved': False,
              'solver_version': clarabel.__version__, 'conic_controls': conic_control(),
              'restart_controls': restart.controls(), 'inner_width': args.width,
              'training_lags': [args.min_lag, args.lag], 'iterations': []}
    seen_counterexamples = set()
    for iteration in range(args.cegar_rounds):
        result = fit(data, args.seconds, args.color)
        if 'linear_coefficients' in result:
            result['holdout'] = holdout(result, args.min_lag, args.lag if args.min_lag == args.lag else 64)
        report['iterations'].append(result)
        report['result'] = result
        report['seconds'] = perf_counter()-began
        args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({'iteration': iteration, **{k: v for k, v in result.items()
              if k not in ('linear_coefficients', 'gram_matrices', 'rational_dual_attempt')},
              'exact_dual_passed': result.get('rational_dual_attempt', {}).get('passed')}), flush=True)
        if 'holdout' not in result or result['holdout']['descent_failures'] == 0:
            break
        counter = result['holdout']['worst']
        key = (counter['row'], counter['center'], counter['lag'])
        if key in seen_counterexamples:
            report['stopped_reason'] = 'Repeated exact training pair still violates numerical fit; no proof claim'
            break
        seen_counterexamples.add(key)
        record = restart.transition(int(counter['row']), counter['center'], counter['lag'])
        assert record is not None
        data.append(record)
    report['seconds'] = perf_counter()-began
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n', encoding='utf-8', newline='\n')
