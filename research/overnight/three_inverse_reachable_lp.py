"""Fit the variation potential only on actual inverse-cone histories.

This diagnoses loss from the ribbon overapproximation. It cannot establish
an all-length certificate; all fits are tested on independent longer cones.
"""

import argparse
import json
from pathlib import Path
import random
from time import perf_counter

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from three_inverse_density_lp import features, ribbon_controls
from three_inverse_weight_beam import extend


def search(depth, seconds, output):
    began = perf_counter()
    rows, rhs = [], []
    states = [(0, 0, 0)]
    levels = []
    for k in range(depth):
        nxt_states = []
        choices = (0, 1) if k % 3 == 0 else (int(k % 3 == 2),)
        for a, b, mode in states:
            old = features(a, b, k, mode) if k >= 2 else None
            for head in choices:
                c = extend(a, b, k, head)
                next_mode = head if k % 3 == 0 else mode
                nxt_states.append((c, a, next_mode))
                if k >= 2:
                    delta = features(c, a, k+1, next_mode)-old
                    delta[96] = -((c >> k) & 1)
                    rows.append(delta)
                    rhs.append(-int(k % 3 == 0 and head != mode))
        states = nxt_states
        if k % 3 == 2:
            levels.append([k+1, len(states), len(rows)])
    matrix = csr_matrix(np.array(rows, dtype=float))
    bound = np.array(rhs, dtype=float)
    objective = np.zeros(97)
    objective[96] = 1
    result = linprog(objective, A_ub=matrix, b_ub=bound,
                     bounds=[(0, None)]*97, method='highs', options={'time_limit': seconds})
    report = {'Lean_verified': False, 'full_problem_solved': False, 'C3w_proved': False,
              'finite_actual_histories_only': True, 'candidate_is_an_unbounded_proof': False,
              'target': 'free-head variation versus initial black weight',
              'depth': depth, 'levels': levels, 'variables': 97, 'constraints': len(rhs),
              'actual_ribbon_coverage_controls': ribbon_controls(),
              'status': int(result.status), 'message': result.message,
              'candidate_accepted': False, 'seconds': perf_counter()-began}
    if result.success:
        report['coefficients'] = result.x.tolist()
        report['coefficient'] = float(result.x[96])
        report['max_training_residual'] = float(np.max(matrix @ result.x-bound))
        rng = random.Random(202610240911)
        checked = failed = 0
        worst = None
        for sample in range(256):
            a = b = mode = 0
            for k in range(384):
                head = rng.randrange(2) if k % 3 == 0 else int(k % 3 == 2)
                c = extend(a, b, k, head)
                next_mode = head if k % 3 == 0 else mode
                if k >= 2:
                    delta = features(c, a, k+1, next_mode)-features(a, b, k, mode)
                    delta[96] = -((c >> k) & 1)
                    reward = int(k % 3 == 0 and head != mode)
                    residual = float(delta @ result.x+reward)
                    checked += 1
                    if residual > 1e-7:
                        failed += 1
                        if worst is None or residual > worst['residual']:
                            worst = {'sample': sample, 'depth': k, 'residual': residual,
                                     'ribbons': [str(a), str(b), str(c)],
                                     'mode': mode, 'head': head, 'actual_reachable': True}
                b, a, mode = a, c, next_mode
        report['holdout'] = {'actual_transitions': checked, 'failures': failed, 'worst': worst}
    report['seconds'] = perf_counter()-began
    output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'coefficients'}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=42)
    parser.add_argument('--seconds', type=int, default=20)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    search(args.depth, args.seconds, args.output)
