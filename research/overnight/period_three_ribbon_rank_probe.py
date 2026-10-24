"""Test a history-dependent period-three rank before unbounded synthesis.

V(current,previous) counts spatial ribbons, keeping an actual finite
predecessor rather than selecting a nonexistent unique inverse. No numerical
fit, infeasibility, or finite control in this file is a Lean theorem.
"""
import argparse
from fractions import Fraction
import json
from itertools import chain
from pathlib import Path
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from period_three_finite_preimage_probe import delta, G
from period_three_prefix_rank_probe import BASE, good, scalar_cycle


def inverse_triple(y, mid_head, old_head):
    first, second = 9+(mid_head << 4), 9+(old_head << 4)
    mid = old = 0
    for i in range(y.bit_length()+65):
        x = (first >> 4) & 1
        w = (second >> 4) & 1
        mid |= x << i
        old |= w << i
        second = delta(second, x)
        first = delta(first, (y >> i) & 1)
    return (mid, old) if first == second == 0 else None


class Model:
    def __init__(self, radius=1, modulus=12, prefix=True):
        self.radius = radius
        self.modulus = modulus
        self.prefix = prefix
        self.patterns = 1 << (2*radius)
        self.flags = 4 if prefix else 1
        self.states = 4*modulus*self.flags
        self.dim = self.states*self.patterns+4

    def features(self, current, previous, padding=12):
        a, b = current & 1, previous & 1
        modes = 2*a+b
        result = {self.dim-4+modes: 1}
        mc = mp = True
        mask = (1 << self.radius)-1
        for i in range(max(current.bit_length(), previous.bit_length())+padding+self.radius):
            x, w = (current >> i) & 1, (previous >> i) & 1
            pattern = ((current >> i) & mask) | (((previous >> i) & mask) << self.radius)
            flags = int(mc)+2*int(mp) if self.prefix else 0
            state = (modes*self.modulus+i % self.modulus)*self.flags+flags
            if pattern or flags:
                index = state*self.patterns+pattern
                result[index] = result.get(index, 0)+1
            mc = mc and x == BASE[a][i % 12]
            mp = mp and w == BASE[b][i % 12]
        assert not mc and not mp
        return result

    def bounds(self):
        bounds = [(None, None)]*self.dim
        for s in range(self.states):
            if s % self.flags == 0:
                bounds[s*self.patterns] = (0, 0)
        return bounds


def controls(model):
    finite = reconstructed = 0
    for old in range(1 << 10):
        assert G(old) == scalar_cycle(old, 10)
        if not good(old):
            continue
        mid, current = G(old), G(G(old))
        if not good(mid):
            continue
        assert inverse_triple(current, mid & 1, old & 1) == (mid, old)
        finite += 1
    for y in range(1 << 13):
        for mid_head in (0, 1):
            for old_head in (0, 1):
                result = inverse_triple(y, mid_head, old_head)
                if result is not None:
                    mid, old = result
                    assert G(old) == mid and G(mid) == y and good(old) and good(mid)
                    reconstructed += 1
    assert reconstructed > 0
    rng = random.Random(202610240748)
    wide = 0
    for _ in range(100000):
        old = rng.getrandbits(rng.randrange(8, 180))
        old = (old & ~7) | rng.choice((0, 7))
        mid = G(old)
        current = G(mid)
        if not good(mid) or not good(current):
            continue
        assert inverse_triple(current, mid & 1, old & 1) == (mid, old)
        assert model.features(current, mid) == model.features(current, mid, 36)
        wide += 1
        if wide == 256:
            break
    assert wide == 256
    # Both valid pasts must remain distinct augmented states.
    assert G(55) == G(56) == 400 and good(55) and good(56) and good(400)
    assert inverse_triple(G(400), 400 & 1, 55 & 1) == (400, 55)
    assert inverse_triple(G(400), 400 & 1, 56 & 1) == (400, 56)
    return {'AllPassed': True, 'packed_vs_scalar_words': 1024,
            'finite_forward_two_cycle_histories': finite,
            'exhaustive_current_words': 8192, 'accepted_inverse_branches': reconstructed,
            'wide_history_and_zero_padding_checks': wide,
            'nonunique_finite_pasts_retained': True, 'Lean_verified': False}


def fit(width, model, seconds=30, reward='flip', wide_draws=0):
    began = time.monotonic()
    values, columns, pointers, rhs = [], [], [0], []
    triples = flips = wide_accepted = maximum_width = 0
    rng = random.Random(202610240750)
    def wide_words():
        for _ in range(wide_draws):
            old = rng.getrandbits(rng.randrange(width+1, 181))
            yield (old & ~7) | rng.choice((0, 7))
    def append(row, bound):
        for j, v in row.items():
            if v:
                columns.append(j)
                values.append(float(v))
        pointers.append(len(values))
        rhs.append(bound)
    for old in chain(range(1 << width), wide_words()):
        if not good(old):
            continue
        current = G(old)
        if not good(current):
            continue
        future = G(current)
        if not good(future):
            continue
        f, g = model.features(current, old), model.features(future, current)
        append({j: -v for j, v in f.items()}, 0)
        change = dict(g)
        for j, v in f.items():
            change[j] = change.get(j, 0)-v
        flip = (current & 1) != (future & 1)
        append(change, -int(flip) if reward == 'flip' else -1)
        triples += 1
        flips += int(flip)
        maximum_width = max(maximum_width, old.bit_length())
        wide_accepted += int(old >= 1 << width)
    matrix = csr_matrix((values, columns, pointers), shape=(len(rhs), model.dim))
    result = linprog(np.zeros(model.dim), A_ub=matrix, b_ub=rhs,
                     bounds=model.bounds(), method='highs-ds', options={'time_limit': seconds})
    report = {'Lean_verified': False, 'full_problem_claim': False, 'C3w_011_proved': False,
              'finite_experiment_only': True, 'current_only_score': False,
              'radius': model.radius, 'modulus': model.modulus, 'prefix_tracking': model.prefix,
              'exhaustive_previous_word_width_bound': width, 'variables': model.dim,
              'additional_wide_draws': wide_draws, 'accepted_wide_histories': wide_accepted,
              'maximum_sampled_previous_width': maximum_width,
              'accepted_history_triples': triples, 'charged_head_flips': flips,
              'reward': reward, 'inequalities': len(rhs), 'status': int(result.status),
              'message': result.message, 'finite_fit_success': bool(result.success),
              'candidate_is_verified_rank': False, 'exact_LP_refutation': False,
              'seconds': round(time.monotonic()-began, 3)}
    if result.success:
        rational = [Fraction(float(x)).limit_denominator(100000) for x in result.x]
        exact = True
        for i, bound in enumerate(rhs):
            value = sum(Fraction(int(v))*rational[j] for j, v in
                        zip(matrix.indices[matrix.indptr[i]:matrix.indptr[i+1]],
                            matrix.data[matrix.indptr[i]:matrix.indptr[i+1]]))
            if value > bound:
                exact = False
                break
        report.update(floating_coefficients=result.x.tolist(),
                      exact_rational_finite_constraints_passed=exact,
                      maximum_floating_constraint_violation=float(np.max(matrix@result.x-np.array(rhs))))
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius', type=int, choices=(1, 2), default=1)
    ap.add_argument('--widths', type=int, nargs='+', default=[12, 16, 20])
    ap.add_argument('--modulus', type=int, choices=(1, 3, 12), default=12)
    ap.add_argument('--without-prefix', action='store_true')
    ap.add_argument('--seconds', type=float, default=30)
    ap.add_argument('--wide-draws', type=int, default=0)
    args = ap.parse_args()
    assert all(8 <= w <= 22 for w in args.widths)
    model = Model(args.radius, args.modulus, not args.without_prefix)
    checked = controls(model)
    print(json.dumps({'controls': checked, 'variables': model.dim}), flush=True)
    report = {'Lean_verified': False, 'full_problem_claim': False, 'controls': checked, 'results': []}
    tag = '-prefix' if model.prefix else ''
    if args.wide_draws:
        tag += '-wide'+str(args.wide_draws)
    path = Path(__file__).with_name(f'period-three-ribbon-r{model.radius}-m{model.modulus}{tag}.json')
    for w in args.widths:
        result = fit(w, model, args.seconds, wide_draws=args.wide_draws)
        report['results'].append(result)
        path.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({k:v for k,v in result.items() if k != 'floating_coefficients'}), flush=True)
        if result['status'] != 0:
            break


if __name__ == '__main__':
    main()
