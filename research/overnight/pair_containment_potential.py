"""Distance-sensitive all-length ranking synthesis for product Rule 30.

No proof claim. The outer row has both extreme black cells strictly outside
the inner row's support. Both supports straddle the observation column. If
this relation and equal current/next center observations forced a uniformly
bounded-below potential to decrease, every eventual period would be excluded.

A finite graph scans arbitrary-length pair words. Affine graph potentials
certify local inequalities at every negative/positive spatial position. The
proposed row potential has nonnegative local counts and distance weights.
"""
import argparse
from collections import deque
from fractions import Fraction
import json
import math
from pathlib import Path
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix


HERE = Path(__file__).resolve().parent


def add(row, index, value):
    if value:
        row[index] = row.get(index, 0)+value
        if not row[index]: del row[index]


def product_table(left, center, right):
    return sum(((30>>((((left>>j)&1)<<2)|(((center>>j)&1)<<1)|((right>>j)&1)))&1)<<j for j in range(2))


class Model:
    def __init__(self, radius):
        self.r = radius; self.patterns = 4**radius; self.headbase = 4*self.patterns; self.dim = self.headbase+4
        self.start = (0, 0, False, False, False)  # buffer, side, begun, last nonzero x-only, seen inner bit on this side
        self.edges = {}; self.reverse = {}; reached = {self.start}; queue = deque([self.start])
        while queue:
            u = queue.popleft(); buf, side, begun, last, seen = u; out = []
            for appended in range(4):
                full = buf|(appended<<(2*(radius+1)))
                letters = [(full>>(2*j))&3 for j in range(radius+2)]
                oldcode = (full>>2)&(self.patterns-1)
                newcode = sum(product_table(*letters[j:j+3])<<(2*j) for j in range(radius))
                current = letters[1]; next_center = newcode&3
                if not begun and current not in [0, 1]: continue
                nb = begun or current != 0; nl = current == 1 if current else last
                ns = seen or bool(current&2); nextbuf = full>>2
                ordinary = (nextbuf, side, nb, nl, ns)
                out.append((u, ordinary, oldcode, newcode, appended, False))
                if side == 0 and seen and current in [0, 3] and next_center in [0, 3]:
                    marked = (nextbuf, 1, nb, nl, False)
                    out.append((u, marked, oldcode, newcode, appended, True))
            self.edges[u] = out
            for edge in out:
                v = edge[1]; self.reverse.setdefault(v, []).append(u)
                if v not in reached: reached.add(v); queue.append(v)
        self.ends = {u for u in reached if u[0] == 0 and u[1] == 1 and u[2] and u[3] and u[4]}
        coreach = set(self.ends); queue = deque(coreach)
        while queue:
            for u in self.reverse.get(queue.popleft(), []):
                if u not in coreach: coreach.add(u); queue.append(u)
        self.vertices = reached&coreach
        self.ends &= self.vertices
        assert self.start in self.vertices and self.ends

    def index(self, side, distance, code): return (side*2+distance)*self.patterns+code

    def gain(self, edge):
        u, v, oldcode, newcode, _, marker = edge
        side = 1 if marker else u[1]; const = {}; slope = {}
        sign = -1 if side == 0 else 1
        if oldcode:
            add(const, self.index(side, 0, oldcode), -1); add(slope, self.index(side, 1, oldcode), -sign)
        if newcode:
            add(const, self.index(side, 0, newcode), 1); add(slope, self.index(side, 1, newcode), sign)
        if marker:
            add(const, self.headbase+(oldcode&3), -1); add(const, self.headbase+(newcode&3), 1)
        return const, slope

    def features(self, row):
        support = [i for i, value in row.items() if value]
        lo, hi = min(support), max(support); vec = {self.headbase+row.get(0, 0): 1}
        for i in range(lo-self.r, hi+1):
            code = sum(row.get(i+j, 0)<<(2*j) for j in range(self.r))
            if not code: continue
            side = int(i >= 0)
            add(vec, self.index(side, 0, code), 1); add(vec, self.index(side, 1, code), abs(i))
        return vec

    def old_cost(self, edge):
        u, v, oldcode, newcode, _, marker = edge; side = 1 if marker else u[1]
        const = {}; slope = {}
        if oldcode:
            add(const, self.index(side, 0, oldcode), 1)
            add(slope, self.index(side, 1, oldcode), -1 if side == 0 else 1)
        if marker: add(const, self.headbase+(oldcode&3), 1)
        return const, slope

    def controls(self, samples=128):
        rng = random.Random(20261024); selected = 0; edgecount = 0
        for _ in range(10000):
            width = rng.randrange(3, 14)
            x = {i: rng.randrange(2) for i in range(-width, width+1)}
            y = {i: rng.randrange(2) for i in range(-width+1, width)}
            x[-width] = x[width] = 1; y[-width+1] = y[width-1] = 1
            row = {i: x.get(i, 0)+2*y.get(i, 0) for i in range(-width, width+1)}
            # Independent scalar update, using the Boolean formula rather than the rule table.
            nx = {i: x.get(i-1, 0)^(x.get(i, 0)|x.get(i+1, 0)) for i in range(-width-1, width+2)}
            ny = {i: y.get(i-1, 0)^(y.get(i, 0)|y.get(i+1, 0)) for i in range(-width, width+1)}
            newrow = {i: nx.get(i, 0)+2*ny.get(i, 0) for i in range(-width-1, width+2)}
            if row[0] not in [0, 3] or newrow[0] not in [0, 3]: continue
            u = self.start; accum = {}
            for i in range(-width-self.r-2, width+self.r+3):
                z = row.get(i+self.r, 0); marker = i == 0
                edge, = [e for e in self.edges[u] if e[4] == z and e[5] == marker]
                assert edge[1] in self.vertices
                const, slope = self.gain(edge)
                for index, value in const.items(): add(accum, index, value)
                for index, value in slope.items(): add(accum, index, i*value)
                u = edge[1]; edgecount += 1
            assert u in self.ends
            expected = self.features(newrow)
            for index, value in self.features(row).items(): add(expected, index, -value)
            assert accum == expected, (accum, expected)
            selected += 1
            if selected == samples: break
        assert selected == samples
        return {'independent_finite_pair_cases': selected, 'scanned_edge_controls': edgecount,
                'exact_feature_accounting_passed': True}

    def solve(self, seconds, signed=False, reward_mode='step', graph_degree=1):
        span = graph_degree+1
        rv = {u: tuple(self.dim+span*j+k for k in range(span)) for j, u in enumerate(sorted(self.vertices))}
        offset = self.dim+span*len(rv)
        qv = {u: tuple(offset+span*j+k for k in range(span)) for j, u in enumerate(sorted(self.vertices))} if signed else {}
        dim = offset+span*len(qv); rows = []; rhs = []
        def append(row, bound=0): rows.append(row); rhs.append(bound)
        def nonpositive(poly, side=None, charge=0):
            if side is None:
                append(dict(poly[0]), -charge); return
            base = -1 if side == 0 else 1; direction = base
            for power in range(span):
                row = {}
                for oldpower in range(power, span):
                    factor = math.comb(oldpower, power)*base**(oldpower-power)*direction**power
                    for index, value in poly[oldpower].items(): add(row, index, factor*value)
                append(row)
        def reward(edge):
            old, new = edge[2]&3, edge[3]&3
            return {'step': 1, 'flip': int(old != new), 'rise': int(old == 0 and new == 3),
                    'fall': int(old == 3 and new == 0), 'black': int(old == 3), 'white': int(old == 0)}[reward_mode]
        def edges_nonpositive(edge, const, slope, auxiliary, charge=0):
            u, v = edge[:2]
            poly = [const, slope]+[{} for _ in range(graph_degree-1)]
            for power in range(span):
                add(poly[power], auxiliary[u][power], 1)
                for low in range(power+1): add(poly[low], auxiliary[v][power], -math.comb(power, low))
            nonpositive(poly, None if edge[5] else u[1], charge)
        nonpositive([{index: -1} for index in rv[self.start]], 0)
        if signed:
            nonpositive([{index: -1} for index in qv[self.start]], 0)
        for u in rv:
            for edge in self.edges[u]:
                v = edge[1]
                if v not in rv: continue
                const, slope = self.gain(edge)
                edges_nonpositive(edge, const, slope, rv, reward(edge) if edge[5] else 0)
                if signed:
                    const, slope = self.old_cost(edge)
                    edges_nonpositive(edge, {j: -v for j, v in const.items()}, {j: -v for j, v in slope.items()}, qv)
        for u in self.ends:
            nonpositive([{index: 1} for index in rv[u]], 1)
            if signed:
                nonpositive([{index: 1} for index in qv[u]], 1)
        values = []; indices = []; indptr = [0]
        for row in rows:
            for index, value in row.items(): values.append(value); indices.append(index)
            indptr.append(len(values))
        matrix = csr_matrix((values, indices, indptr), shape=(len(rows), dim), dtype=float)
        bounds = [(None, None)]*dim if signed else [(0, None)]*self.dim+[(None, None)]*(dim-self.dim)
        for side in range(2):
            for distance in range(2): bounds[self.index(side, distance, 0)] = (0, 0)
        objective = np.zeros(dim)
        if not signed: objective[:self.dim] = 1
        fit = linprog(objective, A_ub=matrix, b_ub=rhs, bounds=bounds, method='highs-ds', options={'time_limit': seconds})
        result = {'unverified_synthesis_only': True, 'Lean_proof': False, 'prize_problem_proved': False,
            'arbitrary_word_lengths_and_spatial_positions': True, 'radius': self.r,
            'graph_vertices': len(rv), 'potential_variables': self.dim, 'auxiliary_variables': dim-self.dim,
            'inequalities': len(rows), 'status': int(fit.status), 'message': fit.message}
        result['signed_weights_with_uniform_graph_lower_bound'] = signed
        result['reward_mode'] = reward_mode
        result['auxiliary_graph_degree'] = graph_degree
        if fit.success:
            rational = [Fraction(float(x)).limit_denominator(100000) for x in fit.x]
            exact = all(sum(value*rational[index] for index, value in row.items()) <= bound for row, bound in zip(rows, rhs))
            exact &= signed or all(x >= 0 for x in rational[:self.dim])
            exact &= all(rational[self.index(side, distance, 0)] == 0 for side in range(2) for distance in range(2))
            result.update(candidate=[str(x) for x in rational], exact_rational_inequalities_passed=bool(exact),
                maximum_float_residual=float(np.max(matrix@fit.x-np.array(rhs))), kernel_check_passed=False)
        return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius', type=int, default=2); ap.add_argument('--seconds', type=int, default=90)
    ap.add_argument('--signed', action='store_true', help='Permit signed row weights with an affine graph proof of nonnegativity')
    ap.add_argument('--reward', choices=['step', 'flip', 'rise', 'fall', 'black', 'white'], default='step')
    ap.add_argument('--graph-degree', type=int, choices=[1, 2], default=1)
    args = ap.parse_args(); started = time.monotonic()
    if not 1 <= args.radius <= 5: raise ValueError('Use radius1..5')
    model = Model(args.radius); controls = model.controls()
    print(json.dumps({'stage': 'controls', **controls}), flush=True)
    report = model.solve(args.seconds, args.signed, args.reward, args.graph_degree); report.update(controls=controls, seconds=round(time.monotonic()-started, 3))
    suffix = '-signed' if args.signed else ''
    if args.reward != 'step': suffix += '-'+args.reward
    if args.graph_degree != 1: suffix += f'-graph-degree{args.graph_degree}'
    (HERE/f'pair-containment-potential-r{args.radius}{suffix}.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'candidate'}))


if __name__ == '__main__': main()
