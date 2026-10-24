"""Falsify a gap score sampled at successive common rising-edge returns.

The two center traces must agree at EVERY observation through the endpoint's
next tick. Endpoints are consecutive 0->1 occurrences. This relaxes the old
one-step condition but would still exclude an infinitely agreeing finite
pair if a natural score strictly decreased at all such returns. No finite
fit proves that condition, any prize statement, or a Lean theorem.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
from time import perf_counter

import numpy as np
from scipy.optimize import linprog

import paired_gap_rank_probe as gap
import paired_nonlocal_rank_probe as pair
from restart_nonlocal_rank_probe import restart_pair


def return_duration(a, b, center, limit=64):
    if not pair.nested(a, b, center):
        return None
    colors = []
    for t in range(limit+2):
        color = (a >> center) & 1
        if color != (b >> center) & 1:
            return None
        if t < 2 and color != t:
            return None
        if t >= 3 and colors[-1] == 0 and color == 1:
            return t-1
        colors.append(color)
        a, b, center = pair.step(a), pair.step(b), center+1
    return None


def record(case):
    a, b, center, duration = case
    assert return_duration(a, b, center, duration) == duration
    old = gap.features(a, b, center)
    for _ in range(duration):
        a, b, center = pair.step(a), pair.step(b), center+1
    assert (a >> center) & 1 == (b >> center) & 1 == 0
    return gap.features(a, b, center)-old


def seed_cases(start, stop, lags):
    row = 1
    cases = []
    for t in range(stop):
        if t >= max(start, 1):
            for lag in lags:
                a, b, c = restart_pair(row, t, lag)
                d = return_duration(a, b, c)
                if d is not None:
                    cases.append((a, b, c, d))
        row = pair.step(row)
    return sorted(set(cases))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--refine-once', action='store_true',
                        help='Promote the first failed holdout to training, then use a fresh later holdout.')
    args = parser.parse_args()
    began = perf_counter()
    report = {'Lean_verified': False, 'full_problem_solved': False,
              'ReturnRanking_proved': False, 'candidate_accepted': False,
              'transition_domain': 'seed', 'sampling': 'successive_common_rising_edges',
              'observations_checked': 'every tick including endpoint+1',
              'features': gap.DIM, 'active_center_zero_features': gap.BASE_DIM,
              'controls': gap.controls()}
    cases = seed_cases(1, 1024, (2, 3, 4, 8, 16, 32))
    assert cases
    report['stages'] = []
    for stage in range(2 if args.refine_once else 1):
        matrix = np.array([record(c) for c in cases])
        rewards = np.ones(len(cases), dtype=np.int64)
        scales = np.maximum(1, abs(matrix).max(axis=0))
        fit = linprog(1/scales, A_ub=matrix/scales, b_ub=-rewards,
                      bounds=(0, None), method='highs', options={'time_limit': 15})
        item = dict(training_cases=len(cases), durations=dict(sorted(Counter(c[3] for c in cases).items())),
                    solver_status=int(fit.status), solver_message=fit.message)
        report['stages'].append(item)
        if fit.success:
            coefficients = fit.x/scales
            report['coefficients'] = coefficients.tolist()
            item['nonzero_coefficients'] = [{'feature': int(j), 'coefficient': float(v)}
                for j, v in enumerate(coefficients) if v > 1e-12]
            item['max_training_residual'] = float(np.max(matrix@coefficients+rewards))
            start, stop = (1024, 4096) if stage==0 else (4096, 8192)
            holdout = seed_cases(start, stop, (2, 3, 4, 8, 16, 32, 64, 128))
            failures = []
            for case in holdout:
                residual = float(record(case)@coefficients+1)
                if residual > 1e-7:
                    a, b, c, d = case
                    failures.append({'outer': str(a), 'inner': str(b), 'center': c,
                                     'duration': d, 'residual': residual})
            item['independent_seed_holdout'] = {'seed_time_range': [start, stop-1],
                'tested_returns': len(holdout), 'failures': len(failures),
                'first_failure': failures[0] if failures else None}
            if stage==0 and args.refine_once and failures:
                item['holdout_promoted_to_next_training'] = True
                report.pop('coefficients', None)
                cases = sorted(set(cases+holdout))
                continue
        elif fit.status == 2:
            dual = gap.exact_dual(matrix, rewards, cases)
            if dual['exact_certificate_passed']:
                duration = {(a, b, c): d for a, b, c, d in cases}
                assert len(duration)==len(cases)
                for term in dual['terms']:
                    term['duration'] = duration[int(term['outer']), int(term['inner']), term['center']]
            report['dual'] = dual
        break
    report['seconds'] = perf_counter()-began
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    summary = {k:v for k,v in report.items() if k not in ('coefficients','dual','stages')}
    summary['stages'] = [{k:v for k,v in s.items() if k not in ('independent_seed_holdout','nonzero_coefficients')} |
        ({'holdout_returns': s['independent_seed_holdout']['tested_returns'],
          'holdout_failures': s['independent_seed_holdout']['failures']}
         if 'independent_seed_holdout' in s else {}) for s in report['stages']]
    print(json.dumps(summary), flush=True)
    if 'dual' in report:
        print(json.dumps({k:v for k,v in report['dual'].items() if k not in ('terms','gains')}), flush=True)


if __name__ == '__main__':
    main()
