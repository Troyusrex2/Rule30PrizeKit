"""All-length graph inequalities for position-weighted ribbon potentials.

Numerical synthesis only. No output is a Lean proof. Position polynomials are
nonnegative on natural positions. Auxiliary graph polynomials have free signs;
coefficient inequalities in x-x0 suffice for every remaining scan position.
"""
import argparse
import json
import math
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from empty_gate_controller import make_controller
from reachable_variation_potential import advance
from synthesize_controlled_cycle_potential import ControlledModel
from synthesize_transducer_potential import HERE, add


class PositionModel(ControlledModel):
    def __init__(self, radius, history, controller, reward, degree):
        super().__init__(radius, history, controller, reward)
        self.degree = degree
        self.base_dim = self.dim
        self.dim *= degree + 1
        self.x0 = history - radius + 2

    def prefix_vector(self, a, b, length, phase, age):
        # Called by the superclass before degree/base_dim are installed.
        if not hasattr(self, 'degree'):
            return super().prefix_vector(a, b, length, phase, age)
        vec = {self.headbase + age: 1}
        for i in range(length-self.r+1):
            code = ((a>>i)&self.full) | (((b>>i)&self.small)<<self.r)
            for degree in range(self.degree+1):
                add(vec, degree*self.base_dim+self.index(0, age, 0, code), (i+1)**degree)
                if i == 0:
                    add(vec, degree*self.base_dim+self.index(0, age, 1, code), 1)
        return vec

    def full_vector(self, a, b, length, phase, age):
        vec = self.prefix_vector(a, b, length, phase, age)
        i = length-self.r
        code = ((a>>i)&self.full) | (((b>>i)&self.small)<<self.r)
        for degree in range(self.degree+1):
            add(vec, degree*self.base_dim+self.index(0, age, 2, code), (i+1)**degree)
        return vec

    def gain_polynomial(self, case, edge, terminal=False):
        old, new = edge[2:4]
        oldage, newage = case['key'][1], case['nextage']
        coeff = [{} for _ in range(self.degree+1)]
        for degree in range(self.degree+1):
            for group in ([0, 2] if terminal else [0]):
                oldidx = degree*self.base_dim+self.index(0, oldage, group, old)
                newidx = degree*self.base_dim+self.index(0, newage, group, new)
                add(coeff[degree], oldidx, -1)
                # The new diagonal is two positions longer.
                for j in range(degree+1):
                    add(coeff[j], newidx, math.comb(degree, j)*2**(degree-j))
        return coeff

    def rebuild_sources(self):
        # Source prefixes were constructed before polynomial setup.
        for case in self.cases:
            old, new = case['key'][1:]
            rebuilt = self.make_controlled_case(old, new)
            case['sources'] = rebuilt['sources']

    def controls(self, samples=12, depth=385):
        rng = random.Random(20261024)
        checked = 0
        vals, successors = self.controller['core_states'], self.controller['successors']
        for _ in range(samples):
            q = rng.randrange(len(vals)); bits = []
            for j in range(self.length):
                bits.append(vals[q]&1)
                if j+1 < self.length: q = rng.choice(successors[q])
            word = sum(bit<<j for j, bit in enumerate(bits)); a = b = 0
            for cycle in range(depth):
                k = 2*cycle; old = self.lookup[word]
                nq = rng.choice(successors[q]); nw = (word>>1)|((vals[nq]&1)<<(self.length-1))
                new = self.lookup[nw]; case = self.case_lookup[(old, new)]
                c = advance(a, b, k, 1-(vals[q]&1)); d = advance(c, a, k+1, 1)
                if (k > self.history and a>>(k-self.s) == 0 and b>>(k-1-self.s) == 0
                        and c>>(k+1-self.s) == 0 and d>>(k+2-self.s) == 0):
                    m = self.history
                    accum = self.prefix_vector(d&((1<<(m+2))-1), c&((1<<(m+1))-1), m+2, 0, new)
                    for j, value in self.prefix_vector(a&((1<<m)-1), b&((1<<(m-1))-1), m, 0, old).items():
                        add(accum, j, -value)
                    u = self.vertex(a, b, c, d, m)
                    assert any(u == v and accum == source for v, source in case['sources'])
                    for i in range(m, k):
                        data = ((a>>i)&1, (b>>i)&1, (c>>(i+1))&1, (d>>(i+2))&1)
                        edge, = [e for e in self.edges[u] if e[4:] == data]
                        coeff = self.gain_polynomial(case, edge, i == k-1)
                        if i == k-1: assert self.terminal(edge, 0)
                        for power, row in enumerate(coeff):
                            for j, value in row.items(): add(accum, j, value*(i-self.r+2)**power)
                        u = edge[1]
                    expected = self.full_vector(d, c, k+2, 0, new)
                    for j, value in self.full_vector(a, b, k, 0, old).items(): add(expected, j, -value)
                    assert accum == expected
                    checked += 1
                a, b, word, q = d, c, nw, nq
        return {'selected_actual_words': checked, 'symbolic_position_accounting_passed': True}

    def solve(self, seconds):
        rows = []; rhs = []; aux = self.dim
        def polynomial_nonpositive(coeff):
            # Express the polynomial in y=x-x0. Nonpositive coefficients
            # imply it is nonpositive for every x>=x0.
            for j in range(self.degree+1):
                row = {}
                for power in range(j, self.degree+1):
                    for index, value in coeff[power].items():
                        add(row, index, value*math.comb(power, j)*self.x0**(power-j))
                rows.append(row); rhs.append(0)
        for case in self.cases:
            rv = {}
            for vertex in sorted(case['vertices']):
                rv[vertex] = list(range(aux, aux+self.degree+1)); aux += self.degree+1
            for u, vec in case['sources']:
                row = dict(vec)
                for power, index in enumerate(rv[u]): add(row, index, -self.x0**power)
                rows.append(row); rhs.append(-case['reward'])
            for u in rv:
                for edge in self.edges[u]:
                    v = edge[1]
                    if v not in rv: continue
                    coeff = self.gain_polynomial(case, edge)
                    for power in range(self.degree+1):
                        add(coeff[power], rv[u][power], 1)
                        for j in range(power+1): add(coeff[j], rv[v][power], -math.comb(power, j))
                    polynomial_nonpositive(coeff)
            for edge in case['ends']:
                coeff = self.gain_polynomial(case, edge, True)
                for power, index in enumerate(rv[edge[0]]): add(coeff[power], index, 1)
                polynomial_nonpositive(coeff)
        values = []; indices = []; indptr = [0]
        for row in rows:
            for index, value in row.items(): values.append(value); indices.append(index)
            indptr.append(len(values))
        matrix = csr_matrix((values, indices, indptr), shape=(len(rows), aux), dtype=float)
        objective = np.zeros(aux); objective[:self.dim] = 1
        fit = linprog(objective, A_ub=matrix, b_ub=rhs,
            bounds=[(0, None)]*self.dim+[(None, None)]*(aux-self.dim), method='highs-ds',
            options={'time_limit': seconds})
        report = {'Lean_proof': False, 'CQ01Empty_proved': False, 'degree': self.degree,
            'all_length_certificate_form': True, 'position_origin': self.x0,
            'potential_variables': self.dim, 'auxiliary_variables': aux-self.dim,
            'inequalities': len(rows), 'status': int(fit.status), 'message': fit.message}
        if fit.success:
            report.update(candidate=fit.x.tolist(), exact_rational_check_passed=False,
                maximum_float_residual=float(np.max(matrix@fit.x-np.array(rhs))))
        return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--head-history', type=int, default=8)
    ap.add_argument('--controller-length', type=int, default=7)
    ap.add_argument('--degree', type=int, default=1)
    ap.add_argument('--reward', choices=['cycle', 'short-gap', 'long-gap'], default='short-gap')
    ap.add_argument('--seconds', type=int, default=120)
    args = ap.parse_args(); started = time.monotonic()
    model = PositionModel(args.radius, args.head_history, make_controller(args.controller_length), args.reward, args.degree)
    model.rebuild_sources()
    controls = model.controls(); print(json.dumps({'stage': 'controls', **controls}), flush=True)
    report = model.solve(args.seconds)
    report.update(controls=controls, radius=args.radius, head_history=args.head_history,
        controller_length=args.controller_length, reward=args.reward, seconds=round(time.monotonic()-started, 3))
    target = HERE/f'position-transducer-r{args.radius}-degree{args.degree}-head{args.head_history}-memory{args.controller_length}-{args.reward}.json'
    target.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'candidate'}))


if __name__ == '__main__': main()
