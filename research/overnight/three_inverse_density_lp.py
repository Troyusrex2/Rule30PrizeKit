"""Try a local amortized density potential for C3 inverse anti-diagonals.

The inequalities are sampled at bounded ribbon lengths, so feasibility is
only a candidate. Infeasibility is numerical and rejects only this model.
No potential is adopted without an all-length certificate and Lean replay.
"""

import argparse
from fractions import Fraction
import json
from pathlib import Path
import random
from time import perf_counter

import numpy as np
from scipy.optimize import linprog

from three_inverse_weight_beam import extend, controls
from three_inverse_cone_probe import forward_packed


def allowed(time, bit):
    return time % 3 == 0 or bit == int(time % 3 == 2)


def features(a, b, k, mode=None):
    states = 3 if mode is None else 6
    phase = k % 3 if mode is None else 2*(k % 3)+mode
    out = np.zeros(16*states+1, dtype=np.int16)
    for i in range(k-1):
        code = 4*((a >> i) & 1)+2*((a >> (i+1)) & 1)+((b >> i) & 1)
        out[phase*8+code] += 1
    out[8*states+phase*4+2*(a & 1)+(b & 1)] += 1
    out[12*states+phase*4+2*((a >> (k-1)) & 1)+((b >> (k-2)) & 1)] += 1
    return out


def ribbon_controls():
    rng = random.Random(202610240858)
    checked = 0
    for _ in range(64):
        a = b = mode = 0
        for k in range(128):
            if k >= 2:
                transitions = (a ^ (a >> 1)) & ((1 << (k-1))-1)
                boundary = int((k-2) % 3 == 1)
                assert not (b & ~transitions)
                assert not (transitions & ~((b | (b << 1)) | boundary))
                assert (transitions & 1) == ((b & 1) | boundary)
                assert allowed(k-1, a & 1) and allowed(k-2, b & 1)
                assert k % 3 != 1 or mode == a & 1
                assert k % 3 != 2 or mode == b & 1
                checked += 1
            head = rng.randrange(2) if k % 3 == 0 else int(k % 3 == 2)
            if k % 3 == 0:
                mode = head
            b, a = a, extend(a, b, k, head)
    return checked


def run(width, signed, upper, graph_lower=False, variation=False):
    began = perf_counter()
    checks = controls()
    ribbons = ribbon_controls()
    rows, rhs = [], []
    states = 6 if variation else 3
    base_dim = 16*states+1
    cost_index = base_dim-1
    per_width = []
    for k in range(2, width+1):
        for a in range(1 << k):
            if not allowed(k-1, a & 1):
                continue
            transitions = (a ^ (a >> 1)) & ((1 << (k-1))-1)
            b = transitions
            while True:
                head_ok = allowed(k-2, b & 1) and (transitions & 1) == ((b & 1) | int((k-2) % 3 == 1))
                upper_ok = not upper or not (transitions & ~((b | (b << 1)) | int((k-2) % 3 == 1)))
                if head_ok and upper_ok:
                    for mode in ((0, 1) if variation else (None,)):
                        if variation and ((k % 3 == 1 and mode != a & 1)
                                          or (k % 3 == 2 and mode != b & 1)):
                            continue
                        old = features(a, b, k, mode)
                        for head in ((0, 1) if k % 3 == 0 else (int(k % 3 == 2),)):
                            c = extend(a, b, k, head)
                            next_mode = head if variation and k % 3 == 0 else mode
                            new = features(c, a, k+1, next_mode)
                            assert not (a & ~((c ^ (c >> 1)) & ((1 << k)-1)))
                            delta = new-old
                            delta[cost_index] = -((c >> k) & 1)
                            rows.append(delta)
                            reward = int(k % 3 == 0 and head != mode) if variation else 1
                            rhs.append(-reward)
                            if signed and not graph_lower:
                                rows.extend((-old, -new))
                                rhs.extend((0, 0))
                if b == 0:
                    break
                b = (b-1) & transitions
        per_width.append([k, len(rows)])
    if graph_lower:
        assert signed and upper
        rows = [np.pad(row, (0, 4*states)) for row in rows]
        for state in range(states):
            phase = state//2 if variation else state
            mode = state % 2 if variation else None
            for a in (0, 1):
                for before in (0, 1):
                    for nxt in (0, 1):
                        for b in (0, 1):
                            change = a ^ nxt
                            if not (b <= change <= (b | before)):
                                continue
                            row = np.zeros(base_dim+4*states)
                            row[state*8+4*a+2*nxt+b] = -1
                            row[base_dim+state*4+2*a+before] -= 1
                            row[base_dim+state*4+2*nxt+b] += 1
                            rows.append(row)
                            rhs.append(0)
            boundary = int((phase-2) % 3 == 1)
            for a in (0, 1):
                for b in (0, 1):
                    if (allowed(phase-1, a) and allowed(phase-2, b)
                            and not (variation and ((phase == 1 and mode != a)
                                                    or (phase == 2 and mode != b)))):
                        row = np.zeros(base_dim+4*states)
                        row[8*states+state*4+2*a+b] = -1
                        row[base_dim+state*4+2*a+boundary] = 1
                        rows.append(row)
                        rhs.append(0)
                    row = np.zeros(base_dim+4*states)
                    row[12*states+state*4+2*a+b] = -1
                    row[base_dim+state*4+2*a+b] = -1
                    rows.append(row)
                    rhs.append(0)
    dim = base_dim+4*states if graph_lower else base_dim
    matrix = np.array(rows, dtype=float)
    bound = np.array(rhs, dtype=float)
    objective = np.zeros(dim)
    objective[cost_index] = 1
    bounds = [(None, None)]*dim if signed else [(0, None)]*dim
    bounds[cost_index] = (0, None)
    result = linprog(objective, A_ub=matrix, b_ub=bound, bounds=bounds,
                     method='highs', options={'time_limit': 15})
    out = {'Lean_verified': False, 'full_problem_solved': False, 'C3w_proved': False,
           'finite_LP_only': True, 'signed': signed, 'upper_ribbon_constraint': upper,
           'width': width, 'variables': dim, 'constraints': len(rhs), 'per_width': per_width,
           'lower_bound_graph_inequalities': graph_lower,
           'target': 'free-head variation versus initial black weight' if variation else 'positive initial black density',
           'roundtrip_controls': checks, 'status': int(result.status), 'message': result.message,
           'actual_ribbon_coverage_controls': ribbons,
           'candidate_is_an_unbounded_proof': False, 'seconds': perf_counter()-began}
    if result.success:
        out.update(coefficient=float(result.x[cost_index]), coefficients=result.x.tolist(),
                   rational_guess=[str(Fraction(float(x)).limit_denominator(10000)) for x in result.x],
                   max_floating_residual=float(np.max(matrix @ result.x-bound)))
        if signed and not variation and not graph_lower:
            rational = [Fraction(x) for x in out['rational_guess']]
            rng = random.Random(202610240856)
            rejection = None
            for sample in range(64):
                a = b = row = trace = 0
                for k in range(160):
                    head = rng.randrange(2) if k % 3 == 0 else int(k % 3 == 2)
                    b, a = a, extend(a, b, k, head)
                    row |= ((a >> k) & 1) << k
                    trace |= head << k
                    if k+1 >= 2:
                        value = sum(int(x)*y for x, y in zip(features(a, b, k+1), rational))
                        if value < 0:
                            assert forward_packed(row, k+1) == trace
                            rejection = {'sample': sample, 'depth': k+1, 'potential': str(value),
                                         'anti_diagonals': [str(a), str(b)], 'row': str(row),
                                         'trace': str(trace), 'actual_reachable': True,
                                         'independent_forward_check_passed': True}
                            break
                if rejection is not None:
                    break
            out['rejected_candidate'] = rejection
            out['candidate_accepted'] = False
    return out


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--width', type=int, default=10)
    parser.add_argument('--signed', action='store_true')
    parser.add_argument('--no-upper', action='store_true')
    parser.add_argument('--graph-lower', action='store_true')
    parser.add_argument('--variation', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = run(args.width, args.signed or args.graph_lower, not args.no_upper, args.graph_lower, args.variation)
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items() if k not in ('coefficients', 'rational_guess')}))
