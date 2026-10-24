"""Test the nonlocal quadratic rank cone on the actual single-seed orbit.

No arbitrary-start obstruction is substituted for the prize target. Every
training pair is (row(t+P),row(t)), with its physical center aligned. Finite
fitting or numerical infeasibility is not a proof of any prize statement.
"""

import argparse
import json
from pathlib import Path
from time import perf_counter

import numpy as np

import paired_nonlocal_rank_probe as pair
from restart_prefix_sdp import conic_control, fit, score


def seed_rows(n):
    rows = [1]
    mirror = 1
    for t in range(n):
        rows.append(pair.step(rows[-1]))
        mirror ^= (mirror << 1) | (mirror << 2)
        # Independent right-to-left packing from MovingFrameBarrierResearch.
        reversed_bits = int(bin(rows[-1])[2:][::-1], 2)
        assert reversed_bits == mirror
        assert rows[-1].bit_length() == 2*(t+1)+1 and rows[-1] & 1
    return rows


def record(rows, t, lag):
    a, b, center = rows[t+lag], rows[t] << lag, t+lag
    na, nb = rows[t+lag+1], rows[t+1] << lag
    assert pair.nested(a, b, center) and na == pair.step(a) and nb == pair.step(b)
    if (a >> center) & 1 != (b >> center) & 1 or (na >> (center+1)) & 1 != (nb >> (center+1)) & 1:
        return None
    old = pair.features(a, b, center)
    new = pair.features(na, nb, center+1)
    reward = int(((a >> center) & 1) != ((na >> (center+1)) & 1))
    return a, b, center, old, new, reward


def run(times, min_lag, max_lag, seconds, output, color=False):
    began = perf_counter()
    rows = seed_rows(max(times)+max_lag+258)
    records = []
    report = {'Lean_verified': False, 'full_problem_solved': False, 'rank_proved': False,
              'single_seed_only': True, 'conic_controls': conic_control(),
              'mirror_packing_controls': len(rows)-1, 'lags': [min_lag, max_lag], 'results': []}
    last_time = 0
    for max_time in times:
        for t in range(last_time+1, max_time+1):
            for lag in range(min_lag, max_lag+1):
                rec = record(rows, t, lag)
                if rec is not None:
                    records.append(rec)
        last_time = max_time
        result = fit(records, seconds, color)
        result['max_seed_time'] = max_time
        if 'linear_coefficients' in result:
            weights = np.array(result['linear_coefficients'])
            Q = np.array(result['gram_matrices'])
            count = failed = negative = 0
            worst = None
            for t in range(max_time+1, max_time+257):
                for lag in range(min_lag, max_lag+1):
                    rec = record(rows, t, lag)
                    if rec is None:
                        continue
                    old, new = score(rec, weights, Q), score(rec, weights, Q, True)
                    residual = new-old+rec[5]
                    count += 1
                    negative += int(min(old, new) < -1e-6)
                    if residual > 1e-6:
                        failed += 1
                        if worst is None or residual > worst['residual']:
                            worst = {'seed_time': t, 'lag': lag, 'residual': residual,
                                     'reward': rec[5], 'old_score': old, 'new_score': new}
            result['holdout'] = {'actual_seed_pairs': count, 'descent_failures': failed,
                                 'negative_values': negative, 'worst': worst}
        report['results'].append(result)
        report['seconds'] = perf_counter()-began
        output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({k: v for k, v in result.items()
              if k not in ('linear_coefficients', 'gram_matrices', 'rational_dual_attempt')})+
              ' exact_dual_passed='+str(result.get('rational_dual_attempt', {}).get('passed')), flush=True)
        if result['status'] not in ('Solved', 'AlmostSolved'):
            break
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--times', type=int, nargs='+', default=[16, 32, 64])
    parser.add_argument('--min-lag', type=int, default=2)
    parser.add_argument('--lag', type=int, default=16)
    parser.add_argument('--seconds', type=int, default=20)
    parser.add_argument('--color', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(args.times, args.min_lag, args.lag, args.seconds, args.output, args.color)
