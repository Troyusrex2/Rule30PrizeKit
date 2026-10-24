"""Search positional potentials on an actual row and its time-shifted image.

Unlike the product-row experiment, the two compared observations are computed
from one finite initial row by the Rule 30 rule table. No solver result is a
Lean proof. The graph certificate, if found, is sufficient for arbitrary
finite word lengths, not just sampled rows.
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


def add(row, index, value):
    if value:
        row[index] = row.get(index, 0)+value
        if not row[index]:
            del row[index]


def local_rule(a, b, c):
    return (30 >> ((a << 2) | (b << 1) | c)) & 1


def column(window, size, center, times):
    bits = [(window >> j) & 1 for j in range(size)]
    result = [bits[center]]
    for t in range(1, times+1):
        bits = [local_rule(*bits[j:j+3]) for j in range(len(bits)-2)]
        result.append(bits[center-t])
    return result


class Model:
    def __init__(self, radius, lag, stride, alternate):
        self.r, self.lag, self.stride, self.alternate = radius, lag, stride, alternate
        self.anchor = lag+stride
        self.size = max(2*self.anchor+1, self.anchor+radius+stride)
        self.patterns = 1 << radius
        self.headbase = 4*self.patterns
        self.dim = self.headbase+2
        self.start = (0, 0, False)
        self.edges = {}
        self.reverse = {}
        reached = {self.start}
        queue = deque(reached)
        while queue:
            u = queue.popleft()
            buf, side, seen = u
            out = []
            for appended in [0, 1]:
                full = buf | (appended << (self.size-1))
                old = (full >> self.anchor) & (self.patterns-1)
                c = column(full, self.size, self.anchor, self.lag+self.stride)
                bits = [(full >> j) & 1 for j in range(self.size)]
                for _ in range(self.stride):
                    bits = [local_rule(*bits[j:j+3]) for j in range(len(bits)-2)]
                new = sum(bits[self.anchor-self.stride+j] << j for j in range(radius))
                ordinary = (full >> 1, side, seen or bool(old & 1))
                out.append((u, ordinary, old, new, appended, False, 0))
                if (side == 0 and seen
                        and all(c[t] == c[t+self.lag] for t in range(self.stride+1))
                        and (not alternate or all(c[t] != c[t+1] for t in range(len(c)-1)))):
                    marked = (full >> 1, 1, False)
                    out.append((u, marked, old, new, appended, True,
                                sum(c[t] != c[t+1] for t in range(self.stride))))
            self.edges[u] = out
            for e in out:
                self.reverse.setdefault(e[1], []).append(u)
                if e[1] not in reached:
                    reached.add(e[1]); queue.append(e[1])
        self.ends = {u for u in reached if u[0] == 0 and u[1] == 1 and u[2]}
        coreach = set(self.ends); queue = deque(coreach)
        while queue:
            for u in self.reverse.get(queue.popleft(), []):
                if u not in coreach:
                    coreach.add(u); queue.append(u)
        self.vertices = reached & coreach
        self.ends &= self.vertices
        assert self.start in self.vertices

    def index(self, side, distance, pattern):
        return (2*side+distance)*self.patterns+pattern

    def gain(self, edge):
        u, _, old, new, _, marker, _ = edge
        side = 1 if marker else u[1]
        sign = 1 if side else -1
        const, slope = {}, {}
        for pattern, change in [(old, -1), (new, 1)]:
            if pattern:
                add(const, self.index(side, 0, pattern), change)
                add(slope, self.index(side, 1, pattern), sign*change)
        if marker:
            add(const, self.headbase+(old & 1), -1)
            add(const, self.headbase+(new & 1), 1)
        return const, slope

    def features(self, row):
        support = [j for j, b in row.items() if b]
        result = {self.headbase+row.get(0, 0): 1}
        for i in range(min(support)-self.r, max(support)+1):
            pattern = sum(row.get(i+j, 0) << j for j in range(self.r))
            if pattern:
                add(result, self.index(int(i >= 0), 0, pattern), 1)
                add(result, self.index(int(i >= 0), 1, pattern), abs(i))
        return result

    def controls(self, samples=128):
        rng = random.Random(20261024)
        accepted = 0
        for _ in range(100000):
            width = rng.randrange(max(5, self.lag+self.stride), 18)
            row = {i: rng.randrange(2) for i in range(-width, width+1)}
            row[-width] = row[width] = 1
            history = [row]
            # Independent formula rather than the graph's truth-table update.
            for t in range(self.lag+self.stride):
                old = history[-1]
                history.append({i: old.get(i-1, 0) ^ (old.get(i, 0) | old.get(i+1, 0))
                                for i in range(-width-t-1, width+t+2)})
            c = [r[0] for r in history]
            if not all(c[t] == c[t+self.lag] for t in range(self.stride+1)):
                continue
            if self.alternate and not all(c[t] != c[t+1] for t in range(len(c)-1)):
                continue
            u = self.start; accum = {}; reward = 0
            for i in range(-width-self.size, width+self.size+1):
                appended = row.get(i+self.size-1-self.anchor, 0)
                edge, = [e for e in self.edges[u] if e[4] == appended and e[5] == (i == 0)]
                assert edge[1] in self.vertices
                const, slope = self.gain(edge)
                for j, v in const.items(): add(accum, j, v)
                for j, v in slope.items(): add(accum, j, i*v)
                reward += edge[6]
                u = edge[1]
            assert u in self.ends
            expected = self.features(history[self.stride])
            for j, v in self.features(row).items(): add(expected, j, -v)
            assert accum == expected
            assert reward == sum(c[t] != c[t+1] for t in range(self.stride))
            accepted += 1
            if accepted == samples:
                break
        assert accepted == samples
        return {'independent_scalar_cases': samples, 'feature_accounting_passed': True,
                'time_shift_correlation_checked': True}

    def solve(self, seconds):
        rv = {u: (self.dim+2*j, self.dim+2*j+1) for j, u in enumerate(sorted(self.vertices))}
        dim = self.dim+2*len(rv)
        rows, rhs = [], []

        def nonpositive(const, slope, side=None, reward=0):
            if side is None:
                rows.append(const); rhs.append(-reward)
                return
            # Affine polynomial on i=-1-k or i=1+k for k>=0.
            sign = 1 if side else -1
            shifted = dict(const)
            for j, v in slope.items(): add(shifted, j, sign*v)
            rows.append(shifted); rhs.append(0)
            rows.append({j: sign*v for j, v in slope.items()}); rhs.append(0)

        nonpositive({rv[self.start][0]: -1}, {rv[self.start][1]: -1}, 0)
        for u in rv:
            for edge in self.edges[u]:
                v = edge[1]
                if v not in rv:
                    continue
                const, slope = self.gain(edge)
                add(const, rv[u][0], 1); add(const, rv[v][0], -1)
                add(const, rv[v][1], -1)
                add(slope, rv[u][1], 1); add(slope, rv[v][1], -1)
                nonpositive(const, slope, None if edge[5] else u[1], edge[6])
        for u in self.ends:
            nonpositive({rv[u][0]: 1}, {rv[u][1]: 1}, 1)
        data, indices, indptr = [], [], [0]
        for row in rows:
            for j, v in row.items(): indices.append(j); data.append(v)
            indptr.append(len(data))
        matrix = csr_matrix((data, indices, indptr), shape=(len(rows), dim), dtype=float)
        bounds = [(0, None)]*self.dim+[(None, None)]*(dim-self.dim)
        for side in range(2):
            for distance in range(2): bounds[self.index(side, distance, 0)] = (0, 0)
        objective = np.zeros(dim); objective[:self.dim] = 1
        fit = linprog(objective, A_ub=matrix, b_ub=rhs, bounds=bounds, method='highs-ds',
                      options={'time_limit': seconds})
        result = {'unverified_synthesis_only': True, 'Lean_verified': False,
            'lag': self.lag, 'stride': self.stride, 'require_alternation': self.alternate,
            'local_pattern_length': self.r, 'graph_window': self.size,
            'graph_vertices': len(rv), 'variables': dim, 'inequalities': len(rows),
            'status': int(fit.status), 'message': fit.message,
            'finite_length_bound_imposed': False, 'prize_problem_proved': False}
        if fit.success:
            rational = [Fraction(float(v)).limit_denominator(100000) for v in fit.x]
            exact = all(sum(v*rational[j] for j, v in row.items()) <= bound
                        for row, bound in zip(rows, rhs))
            exact &= all(v >= 0 for v in rational[:self.dim])
            exact &= all(rational[self.index(s, d, 0)] == 0 for s in range(2) for d in range(2))
            result.update(candidate=[str(v) for v in rational], exact_rational_checks_passed=bool(exact),
                          kernel_certificate_verified=False)
        return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius', type=int, default=2)
    ap.add_argument('--lag', type=int, default=2)
    ap.add_argument('--stride', type=int, default=1)
    ap.add_argument('--alternate', action='store_true')
    ap.add_argument('--seconds', type=float, default=60)
    args = ap.parse_args()
    assert args.lag >= 2 and args.stride >= 1
    if args.alternate:
        assert args.lag % 2 == 0
    started = time.monotonic()
    model = Model(args.radius, args.lag, args.stride, args.alternate)
    controls = model.controls()
    result = model.solve(args.seconds)
    result.update(controls=controls, seconds=round(time.monotonic()-started, 3))
    tag = '-alternate' if args.alternate else ''
    output = Path(__file__).with_name(f'lag-correlated-potential-p{args.lag}-s{args.stride}-r{args.radius}{tag}.json')
    output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k != 'candidate'}), flush=True)


if __name__ == '__main__':
    main()
