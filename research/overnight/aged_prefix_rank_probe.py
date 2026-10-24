"""Finite falsification with actual surviving zero-boundary prehistories.

A finite-sample feasible score is not a rank proof. Unlike the whole-word graph
search, this program tests only bounded initial widths. It retains every even
observation in an actual prehistory, not independently chosen endpoint rows.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from stripe_prefix_dfa_potential import Model, scalar_z


def probe(width, age, model, seconds):
    assert age >= 0 and age % 2 == 0
    values, columns, indptr, rhs = [], [], [0], []
    accepted = flips = 0

    def append(row, bound):
        for j, value in row.items():
            if value:
                columns.append(j); values.append(float(value))
        indptr.append(len(values)); rhs.append(bound)

    began = time.monotonic()
    for a in range(1, 1 << width, 2):
        x = a
        valid = True
        for t in range(age//2+2):
            if model.final_mode(x) != 2:
                valid = False
                break
            if t == age//2: old_word = x
            if t < age//2+1: x = scalar_z(scalar_z(x))
        if not valid: continue
        old = model.features(old_word)
        new = model.features(x)
        append({j: -v for j, v in old.items()}, 0)
        gain = dict(new)
        for j, value in old.items(): gain[j] = gain.get(j, 0)-value
        flip = int((old_word >> 1) & 1 != (x >> 1) & 1)
        append(gain, -flip)
        accepted += 1
        flips += flip
    matrix = csr_matrix((values, columns, indptr), shape=(len(rhs), model.dim))
    bounds = [(None, None)]*model.dim
    for state in range(model.states): bounds[model.index(state, 0)] = (0, 0)
    fit = linprog(np.zeros(model.dim), A_ub=matrix, b_ub=rhs, bounds=bounds,
                  method='highs-ds', options={'time_limit': seconds})
    return {'initial_width': width, 'actual_prehistory_steps': age,
        'all_even_intermediate_rows_accepted': True,
        'accepted_initial_words': accepted, 'transitions_charged_for_free_bit_flip': flips,
        'variables': model.dim, 'inequalities': len(rhs), 'status': int(fit.status),
        'message': fit.message, 'finite_sample_feasible_only': bool(fit.success),
        'candidate_is_a_verified_rank': False, 'exact_LP_refutation': False,
        'seconds': round(time.monotonic()-began, 3)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-width', type=int, default=20)
    args = ap.parse_args()
    assert 14 <= args.max_width <= 22
    model = Model(4, True)
    results = []
    for age in [2, 4, 8, 12]:
        for width in range(12, args.max_width+1, 2):
            result = probe(width, age, model, 30)
            results.append(result)
            print(json.dumps(result), flush=True)
            # Once actual finite words refute the candidate class numerically,
            # larger initial widths cannot restore feasibility for this age.
            if result['status'] == 2: break
    report = {'untrusted_finite_experiment_only': True, 'Lean_verified': False,
        'Q01_proved': False, 'prize_problem_proved': False, 'pattern_length': 4,
        'prefix_dfa_states': 12, 'tracks_prefix_ones_parity': True,
        'independent_model_controls': model.controls(), 'results': results}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n',
        encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
