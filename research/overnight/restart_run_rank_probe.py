"""Order-sensitive run potentials for exact lag-two restart pairs.

The previous PSD-moment certificate has negative gains in these omitted
run features, so this is a targeted extension rather than a larger local
window. All coefficients are nonnegative; every feature is a natural
number. Fitting on finite pairs remains untrusted discovery only.
"""

import argparse
from functools import lru_cache
import json
from pathlib import Path
import random
from time import perf_counter

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

import paired_nonlocal_rank_probe as pair
import restart_nonlocal_rank_probe as restart
from restart_prefix_sdp import records_at_widths


KEYS = [(side, mask, metric) for side in (0, 2, 3)
        for mask in range(1, 15) for metric in range(8)]
BASE_DIM = pair.DIM+len(KEYS)
DIM = 2*BASE_DIM


@lru_cache(maxsize=16384)
def run_features(a, b, center):
    cells = pair.letters(a, b, center)
    out = []
    for side in (0, 2, 3):
        word = [s for p, s in cells if side == 3 or pair.region(p) == side]
        for mask in range(1, 15):
            runs = []
            count = 0
            for symbol in word:
                if mask >> symbol & 1:
                    count += 1
                elif count:
                    runs.append(count)
                    count = 0
            if count:
                runs.append(count)
            prefix = 0
            for symbol in word:
                if not (mask >> symbol & 1):
                    break
                prefix += 1
            suffix = 0
            for symbol in reversed(word):
                if not (mask >> symbol & 1):
                    break
                suffix += 1
            out.extend((len(runs), sum(runs), sum(v*v for v in runs),
                        sum(v**3 for v in runs), max(runs, default=0),
                        prefix, suffix, min(runs, default=0)))
    assert len(out) == len(KEYS)
    return np.array(out, dtype=np.int64)


def features(record, updated=False):
    a, b, center, old, new, reward = record
    if updated:
        a, b, center, moments = pair.step(a), pair.step(b), center+1, new
    else:
        moments = old
    mode = (a >> center) & 1
    out = np.zeros(DIM, dtype=np.int64)
    out[mode*BASE_DIM:(mode+1)*BASE_DIM] = np.r_[moments, run_features(a, b, center)]
    return out


def controls():
    rng = random.Random(202610240935)
    checked = 0
    for _ in range(64):
        width = rng.randrange(5, 24)
        center = rng.randrange(2, width-2)
        a = rng.getrandbits(width) | 1 | (1 << (width-1))
        b = rng.getrandbits(width-2) << 1
        cells = pair.letters(a, b, center)
        actual = run_features(a, b, center)
        for side in (0, 2, 3):
            word = [s for p, s in cells if side == 3 or pair.region(p) == side]
            for mask in range(1, 15):
                intervals = sum(all(mask >> s & 1 for s in word[i:j])
                                for i in range(len(word)) for j in range(i+1, len(word)+1))
                offset = KEYS.index((side, mask, 0))
                # Number of matching substrings equals sum l(l+1)/2.
                assert 2*intervals == int(actual[offset+1]+actual[offset+2])
                checked += 1
    return {'brute_substring_vs_run_moment_checks': checked, 'AllPassed': True}


def holdout(coefficients, seed=202610240936, batch=64):
    rng = random.Random(seed)
    checked = failures = 0
    worst = None
    counters = []
    for _ in range(20000):
        width = rng.randrange(3, 65)
        center = rng.randrange(1, width-1)
        row = rng.getrandbits(width) | 1 | (1 << (width-1))
        record = restart.transition(row, center, 2)
        if record is None:
            continue
        old, new = features(record), features(record, True)
        residual = float((new-old) @ coefficients+record[5])
        checked += 1
        if residual > 1e-6:
            failures += 1
            counters.append({'row': str(row), 'center': center, 'lag': 2,
                             'width': width, 'residual': residual, 'reward': record[5]})
            if worst is None or residual > worst['residual']:
                worst = {'row': str(row), 'center': center, 'lag': 2,
                         'width': width, 'residual': residual, 'reward': record[5]}
        if checked == 512:
            break
    assert checked == 512
    counters.sort(key=lambda c: c['residual'], reverse=True)
    return {'actual_restart_transitions': checked, 'descent_failures': failures,
            'worst': worst, 'counterexamples': counters[:batch]}


def run(width, iterations, output, seed_report=None, batch=64):
    began = perf_counter()
    records = records_at_widths(width, 2, 2)
    seen = {(str(r[1] >> 2), r[2]-2) for r in records}
    if seed_report:
        prior = json.loads(seed_report.read_text(encoding='utf-8'))
        for step in prior['iterations']:
            counter = step.get('holdout', {}).get('worst')
            if counter is None:
                continue
            key = (counter['row'], counter['center'])
            if key not in seen:
                rec = restart.transition(int(counter['row']), counter['center'], 2)
                assert rec is not None
                records.append(rec)
                seen.add(key)
    deltas = [features(r, True)-features(r) for r in records]
    rewards = [r[5] for r in records]
    report = {'Lean_verified': False, 'full_problem_solved': False,
              'rank_proved': False, 'nonnegative_natural_features': DIM,
              'lag': 2, 'controls': controls(), 'iterations': [], 'candidate_accepted': False}
    for iteration in range(iterations):
        A = csr_matrix(np.array(deltas, dtype=float))
        rhs = -np.array(rewards, dtype=float)
        scales = np.maximum(1, abs(A).max(axis=0).toarray().ravel())
        scaled = A.multiply(1/scales).tocsr()
        fit = linprog(np.ones(DIM), A_ub=scaled, b_ub=rhs,
                      bounds=[(0, None)]*DIM, method='highs', options={'time_limit': 15})
        item = {'iteration': iteration, 'actual_training_pairs': len(records),
                'status': int(fit.status), 'message': fit.message}
        if fit.success:
            coefficients = fit.x/scales
            item['coefficients'] = coefficients.tolist()
            item['max_training_residual'] = float(np.max(A @ coefficients-rhs))
            item['holdout'] = holdout(coefficients, batch=batch)
            if item['holdout']['descent_failures'] == 0:
                item['fresh_holdout'] = holdout(coefficients, seed=202610240937, batch=batch)
        report['iterations'].append(item)
        report['seconds'] = perf_counter()-began
        output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({'iteration': iteration, 'actual_training_pairs': len(records),
              'status': int(fit.status), 'message': fit.message,
              'holdout_failures': item.get('holdout', {}).get('descent_failures'),
              'fresh_holdout_failures': item.get('fresh_holdout', {}).get('descent_failures')}), flush=True)
        if not fit.success:
            break
        counters = (item.get('fresh_holdout') or item['holdout'])['counterexamples']
        if not counters:
            report['stopped_reason'] = 'Two finite random batches passed; all-length proof still absent'
            break
        added = 0
        for counter in counters:
            key = (counter['row'], counter['center'])
            if key in seen:
                continue
            seen.add(key)
            record = restart.transition(int(counter['row']), counter['center'], 2)
            assert record is not None
            records.append(record)
            deltas.append(features(record, True)-features(record))
            rewards.append(record[5])
            added += 1
        if not added:
            report['stopped_reason'] = 'Repeated numerical counterexample'
            break
    report['seconds'] = perf_counter()-began
    output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--width', type=int, default=8)
    parser.add_argument('--iterations', type=int, default=32)
    parser.add_argument('--seed-report', type=Path)
    parser.add_argument('--batch', type=int, default=64)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(args.width, args.iterations, args.output, args.seed_report, args.batch)
