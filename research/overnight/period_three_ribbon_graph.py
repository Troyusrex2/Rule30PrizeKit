"""Unbounded-word discovery graph for actual finite period-three histories.

Two inverse pipelines read the latest row and generate its two actual past
rows. A one-cell delayed charge supports two-cell spatial ribbon features.
Numerical synthesis is not a theorem; graph coverage still needs Lean proof.
"""
import argparse
from collections import deque
from fractions import Fraction
import json
from pathlib import Path
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from period_three_ribbon_rank_probe import Model as Features, G, good, BASE, delta


def add(d, k, v):
    d[k] = d.get(k, 0)+v
    if not d[k]:
        del d[k]


def admissible(row):
    mode = row & 1
    for i in range(row.bit_length()+12):
        if ((row >> i) & 1) != BASE[mode][i % 12]:
            return i % 3 == 0
    raise AssertionError('A finite row must differ from the reference')


class Model:
    def __init__(self, radius=2, state_limit=200000, restrict_front=False):
        self.features = Features(radius)
        self.dim = self.features.dim
        self.radius = radius
        self.restrict_front = restrict_front
        self.sources = set()
        self.ends = set()
        self.edges = {}
        reverse = {}
        reached = set()
        for mode in range(8):
            yh, xh, wh = (mode >> 2) & 1, (mode >> 1) & 1, mode & 1
            pair = (9+(xh << 4)) | ((9+(wh << 4)) << 6)
            initial = (mode, pair, 7, 0, 0, 0)
            self.sources.add(initial)
            local = {initial}
            queue = deque([initial])
            while queue:
                u = queue.popleft()
                _, pair, previous_match, phase, depth, previous_y = u
                a, b = pair & 63, pair >> 6
                x, w = (a >> 4) & 1, (b >> 4) & 1
                xp, wp = (a >> 5) & 1, (b >> 5) & 1
                if depth == 0:
                    current_match = 7
                else:
                    p = (phase-1) % 12
                    match_bits = int(previous_y == BASE[yh][p])
                    match_bits |= int(xp == BASE[xh][p]) << 1
                    match_bits |= int(wp == BASE[wh][p]) << 2
                    current_match = previous_match & match_bits
                if pair == 0 and previous_match == 0 and previous_y == 0 and depth == 3:
                    self.ends.add(u)
                out = []
                for y in (0, 1):
                    if depth < 3 and y != yh:
                        continue
                    if restrict_front and phase % 3 != 0:
                        if any((current_match & (1 << j)) and bit != BASE[h][phase]
                               for j, bit, h in ((0, y, yh), (1, x, xh), (2, w, wh))):
                            continue
                    target_pair = delta(a, y) | (delta(b, x) << 6)
                    v = (mode, target_pair, current_match, (phase+1) % 12, min(3, depth+1), y)
                    edge = (u, v, y)
                    out.append(edge)
                    reverse.setdefault(v, []).append(u)
                    if v not in local:
                        local.add(v)
                        queue.append(v)
                self.edges[u] = out
                if len(local)+len(reached) > state_limit:
                    raise RuntimeError('Graph state guard reached; no result claimed')
            reached.update(local)
            print(json.dumps({'mode': mode, 'reached': len(local), 'total': len(reached)}), flush=True)
        live = set(self.ends)
        queue = deque(live)
        while queue:
            for u in reverse.get(queue.popleft(), []):
                if u not in live:
                    live.add(u)
                    queue.append(u)
        self.vertices = reached & live
        self.sources &= self.vertices
        assert len(self.sources) == 8

    def feature_index(self, current_mode, previous_mode, phase, flags, pattern):
        state = ((2*current_mode+previous_mode)*12+phase)*4+flags
        return state*self.features.patterns+pattern

    def gain(self, edge, old_only=False):
        u, _, y = edge
        mode, pair, previous_match, phase, depth, previous_y = u
        yh, xh, wh = (mode >> 2) & 1, (mode >> 1) & 1, mode & 1
        a, b = pair & 63, pair >> 6
        x, w = (a >> 4) & 1, (b >> 4) & 1
        xp, wp = (a >> 5) & 1, (b >> 5) & 1
        result = {}
        if depth == 0:
            add(result, self.dim-4+2*xh+wh, -1)
            if not old_only:
                add(result, self.dim-4+2*yh+xh, 1)
        else:
            old_flags = ((previous_match >> 1) & 1)+2*((previous_match >> 2) & 1)
            new_flags = (previous_match & 1)+2*((previous_match >> 1) & 1)
            xx = xp | ((x << 1) if self.radius == 2 else 0)
            ww = wp | ((w << 1) if self.radius == 2 else 0)
            yy = previous_y | ((y << 1) if self.radius == 2 else 0)
            old_pattern = xx | (ww << self.radius)
            new_pattern = yy | (xx << self.radius)
            if old_flags or old_pattern:
                add(result, self.feature_index(xh, wh, (phase-1) % 12, old_flags, old_pattern), -1)
            if not old_only and (new_flags or new_pattern):
                add(result, self.feature_index(yh, xh, (phase-1) % 12, new_flags, new_pattern), 1)
        return result

    def controls(self):
        rng = random.Random(202610240756)
        accepted = 0
        for _ in range(100000):
            w = rng.getrandbits(rng.randrange(8, 181))
            w = (w & ~7) | rng.choice((0, 7))
            x, y = G(w), G(G(w))
            if not good(x) or not good(y):
                continue
            if self.restrict_front and not all(admissible(row) for row in (w, x, y)):
                continue
            mode = ((y & 1) << 2) | ((x & 1) << 1) | (w & 1)
            pair = (9+((x & 1) << 4)) | ((9+((w & 1) << 4)) << 6)
            u = (mode, pair, 7, 0, 0, 0)
            assert u in self.sources
            actual = {}
            for k in range(y.bit_length()+24):
                assert ((u[1] >> 4) & 1) == ((x >> k) & 1)
                assert ((u[1] >> 10) & 1) == ((w >> k) & 1)
                bit = (y >> k) & 1
                edge, = [e for e in self.edges[u] if e[2] == bit]
                assert edge[1] in self.vertices
                for j, v in self.gain(edge).items():
                    add(actual, j, v)
                u = edge[1]
            assert u in self.ends
            expected = self.features.features(y, x)
            for j, v in self.features.features(x, w).items():
                add(expected, j, -v)
            assert actual == expected
            accepted += 1
            if accepted == 256:
                break
        assert accepted == 256
        return {'AllPassed': True, 'finite_histories_and_delayed_feature_accounts': accepted,
                'graph_coverage_Lean_verified': False}

    def solve(self, seconds, method='highs-ds'):
        vertices = sorted(self.vertices)
        offsets = {u: self.dim+i for i, u in enumerate(vertices)}
        offset2 = self.dim+len(vertices)
        old_offsets = {u: offset2+i for i, u in enumerate(vertices)}
        dim = self.dim+2*len(vertices)
        data, cols, ptr, rhs = [], [], [0], []
        def append(row, bound):
            for j, v in row.items():
                if v:
                    cols.append(j)
                    data.append(float(v))
            ptr.append(len(data))
            rhs.append(bound)
        for s in self.sources:
            append({offsets[s]: -1}, 0)
            append({old_offsets[s]: -1}, 0)
        edges = 0
        for u in vertices:
            for edge in self.edges[u]:
                v = edge[1]
                if v not in self.vertices:
                    continue
                edges += 1
                charge = int(u[4] == 0 and ((u[0] >> 1) & 1) != ((u[0] >> 2) & 1))
                for old_only, potentials in ((False, offsets), (True, old_offsets)):
                    row = self.gain(edge, old_only)
                    add(row, potentials[u], 1)
                    add(row, potentials[v], -1)
                    append(row, 0 if old_only else -charge)
        for e in self.ends:
            if e in self.vertices:
                append({offsets[e]: 1}, 0)
                append({old_offsets[e]: 1}, 0)
        matrix = csr_matrix((data, cols, ptr), shape=(len(rhs), dim))
        bounds = self.features.bounds()+[(None, None)]*(dim-self.dim)
        print(json.dumps({'stage': 'LP', 'vertices': len(vertices), 'edges': edges,
                          'variables': dim, 'inequalities': len(rhs)}), flush=True)
        began = time.monotonic()
        result = linprog(np.zeros(dim), A_ub=matrix, b_ub=rhs, bounds=bounds,
                         method=method, options={'time_limit': seconds})
        report = {'Lean_verified': False, 'full_problem_claim': False, 'C3w_011_proved': False,
                  'unbounded_word_discovery_graph': True, 'actual_two_step_preimages_retained': True,
                  'ribbon_radius': self.radius, 'vertices': len(vertices), 'edges': edges,
                  'first_defects_multiple_of_three': self.restrict_front, 'solver_method': method,
                  'variables': dim, 'inequalities': len(rhs), 'status': int(result.status),
                  'message': result.message, 'candidate_is_verified_rank': False,
                  'exact_LP_refutation': False, 'solve_seconds': round(time.monotonic()-began, 3)}
        if result.success:
            rational = [Fraction(float(x)).limit_denominator(1000000) for x in result.x]
            exact = True
            for i, bound in enumerate(rhs):
                value = sum(int(v)*rational[j] for j, v in
                            zip(matrix.indices[matrix.indptr[i]:matrix.indptr[i+1]],
                                matrix.data[matrix.indptr[i]:matrix.indptr[i+1]]))
                if value > bound:
                    exact = False
                    break
            report.update(exact_rational_graph_constraints_passed=exact,
                          floating_feature_coefficients=result.x[:self.dim].tolist(),
                          maximum_floating_violation=float(np.max(matrix@result.x-np.array(rhs))))
        return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius', type=int, choices=(1, 2), default=2)
    ap.add_argument('--seconds', type=float, default=60)
    ap.add_argument('--restrict-front', action='store_true')
    ap.add_argument('--method', choices=('highs-ds', 'highs-ipm'), default='highs-ds')
    args = ap.parse_args()
    began = time.monotonic()
    model = Model(args.radius, restrict_front=args.restrict_front)
    checked = model.controls()
    print(json.dumps({'controls': checked, 'vertices': len(model.vertices)}), flush=True)
    report = model.solve(args.seconds, args.method)
    report.update(controls=checked, seconds=round(time.monotonic()-began, 3))
    tag = '-front' if args.restrict_front else ''
    if args.method != 'highs-ds':
        tag += '-'+args.method
    path = Path(__file__).with_name('period-three-ribbon-graph-r'+str(args.radius)+tag+'.json')
    path.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'floating_feature_coefficients'}), flush=True)


if __name__ == '__main__':
    main()
