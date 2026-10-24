"""All-length LP with distances from BOTH ends of a moving wavefront word.

Numerical, unverified exploration. Three nonnegative feature channels count
patterns, their distance from the head, and their distance from the moving
tail. Signed graph potentials are affine in scan index and total cut length.
"""
import argparse
import json
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from empty_gate_controller import make_controller
from reachable_variation_potential import advance
from synthesize_front_transducer_potential import FrontModel, finite_row_controls
from synthesize_transducer_potential import HERE, add


class DistanceModel(FrontModel):
    def __init__(self, radius, history, controller, reward, front_parity):
        super().__init__(radius, history, controller, reward, front_parity)
        self.base_dim = self.dim; self.dim *= 3

    def prefix_polynomial(self, a, b, length, age, cut_shift):
        const = {self.headbase+age: 1, 2*self.base_dim+self.headbase+age: cut_shift}
        slope = {2*self.base_dim+self.headbase+age: 1}
        for start in range(length-self.r+1):
            code = ((a>>start)&self.full) | (((b>>start)&self.small)<<self.r)
            for group in ([0, 1] if start == 0 else [0]):
                index = self.index(0, age, group, code)
                add(const, index, 1)
                add(const, self.base_dim+index, start+1)
                add(const, 2*self.base_dim+index, cut_shift-self.r-start)
                add(slope, 2*self.base_dim+index, 1)
        return [const, {}, slope]  # constant, scan-index coefficient, cut coefficient

    def source_polynomial(self, case):
        old, new = case['key'][1:]; word = self.words[old]; m = self.history; a = b = 0
        for j in range(m//2):
            past = (word>>(self.length-1-m//2+j))&1
            c = advance(a, b, 2*j, 1-past); d = advance(c, a, 2*j+1, 1); a, b = d, c
        h = 1-((word>>(self.length-1))&1)
        c = advance(a, b, m, h); d = advance(c, a, m+1, 1)
        poly = self.prefix_polynomial(d, c, m+2, new, 1)
        for power, row in enumerate(self.prefix_polynomial(a, b, m, old, 0)):
            for index, value in row.items(): add(poly[power], index, -value)
        return poly

    def gain_polynomial(self, case, edge, terminal=False):
        old, new = edge[2:4]; oa, na = case['key'][1], case['nextage']
        poly = [{}, {}, {}]
        # Old start=i-r+1, new start=i-r+3.
        # Old tail distance=K-i-1; new tail distance=K-i-2.
        for age, code, sign, new_side in [(oa, old, -1, False), (na, new, 1, True)]:
            if terminal and new_side: continue
            index = self.index(0, age, 0, code)
            add(poly[0], index, sign)
            add(poly[0], self.base_dim+index, sign*(4-self.r if new_side else 2-self.r))
            add(poly[1], self.base_dim+index, sign)
            add(poly[0], 2*self.base_dim+index, -sign*(2 if new_side else 1))
            add(poly[1], 2*self.base_dim+index, -sign)
            add(poly[2], 2*self.base_dim+index, sign)
        if terminal:
            small = (1<<(self.r-1))-1; lower = (1<<(self.r-2))-1
            ot = ((old>>1)&small) | (((old>>(self.r+1))&lower)<<(self.r-1))
            nt = (new&small) | (((new>>self.r)&lower)<<(self.r-1))
            add(poly[0], self.index(0, oa, 2, ot), -1)
            add(poly[0], self.index(0, na, 2, nt), 1)
        return poly

    @staticmethod
    def evaluate(poly, scan, cut):
        vec = {}
        for row, factor in zip(poly, [1, scan, cut]):
            for index, value in row.items(): add(vec, index, value*factor)
        return vec

    def full_features(self, a, b, cut, age):
        vec = self.evaluate(self.prefix_polynomial(a, b, cut, age, 0), 0, cut)
        start = cut-self.r+1
        tail = ((a>>start)&((1<<(self.r-1))-1)) | (((b>>start)&((1<<(self.r-2))-1))<<(self.r-1))
        add(vec, self.index(0, age, 2, tail), 1)
        return vec

    def controls(self, samples=12, depth=385):
        rng = random.Random(20261024); vals = self.controller['core_states']; succ = self.controller['successors']; checked = 0
        for _ in range(samples):
            q = rng.randrange(len(vals)); bits = []
            for j in range(self.length):
                bits.append(vals[q]&1)
                if j+1 < self.length: q = rng.choice(succ[q])
            word = sum(bit<<j for j, bit in enumerate(bits)); a = b = 0
            for cycle in range(depth):
                n = 2*cycle; old = self.lookup[word]; nq = rng.choice(succ[q])
                nw = (word>>1)|((vals[nq]&1)<<(self.length-1)); new = self.lookup[nw]; case = self.case_lookup[(old, new)]
                c = advance(a, b, n, 1-(vals[q]&1)); d = advance(c, a, n+1, 1); cut = a.bit_length()
                if (cut > self.history and b.bit_length() == cut-1+self.front_parity and
                        c.bit_length() == cut+self.front_parity and d.bit_length() == cut+1):
                    accum = self.evaluate(self.source_polynomial(case), self.history, cut)
                    u = self.vertex(a, b, c, d, self.history)
                    assert any(u == v for v, _ in case['sources'])
                    for i in range(self.history, cut):
                        data = ((a>>i)&1, (b>>i)&1, (c>>(i+1))&1, (d>>(i+2))&1)
                        edge, = [e for e in self.edges[u] if e[4:] == data]
                        if i == cut-1: assert self.terminal(edge, 0)
                        for index, value in self.evaluate(self.gain_polynomial(case, edge, i == cut-1), i, cut).items():
                            add(accum, index, value)
                        u = edge[1]
                    expected = self.full_features(d, c, cut+1, new)
                    for index, value in self.full_features(a, b, cut, old).items(): add(expected, index, -value)
                    assert accum == expected
                    checked += 1
                a, b, word, q = d, c, nw, nq
        return {'selected_actual_words': checked, 'both_distance_accounting_passed': True}

    def solve(self, seconds):
        rows = []; rhs = []; aux = self.dim; m = self.history
        def append(row, bound=0): rows.append(row); rhs.append(bound)
        def combine(a, b):
            row = dict(a)
            for index, value in b.items(): add(row, index, value)
            return row
        for case in self.cases:
            rv = {}
            for v in sorted(case['vertices']): rv[v] = list(range(aux, aux+3)); aux += 3
            for u, _ in case['sources']:
                poly = self.source_polynomial(case)
                for power, index in enumerate(rv[u]): add(poly[power], index, -1)
                append(dict(poly[2]))
                append(self.evaluate(poly, m, m+1), -case['reward'])
            for u in rv:
                for edge in self.edges[u]:
                    v = edge[1]
                    if v not in rv: continue
                    poly = self.gain_polynomial(case, edge)
                    for power in range(3):
                        add(poly[power], rv[u][power], 1); add(poly[power], rv[v][power], -1)
                    add(poly[0], rv[v][1], -1)
                    # i=m+x, K=i+2+y, x,y>=0.
                    append(combine(poly[1], poly[2])); append(dict(poly[2]))
                    append(self.evaluate(poly, m, m+2))
            for edge in case['ends']:
                poly = self.gain_polynomial(case, edge, True)
                for power, index in enumerate(rv[edge[0]]): add(poly[power], index, 1)
                # K=i+1, i=m+x.
                append(combine(poly[1], poly[2])); append(self.evaluate(poly, m, m+1))
        values = []; indices = []; indptr = [0]
        for row in rows:
            for index, value in row.items(): values.append(value); indices.append(index)
            indptr.append(len(values))
        matrix = csr_matrix((values, indices, indptr), shape=(len(rows), aux), dtype=float)
        objective = np.zeros(aux); objective[:self.dim] = 1
        fit = linprog(objective, A_ub=matrix, b_ub=rhs,
            bounds=[(0, None)]*self.dim+[(None, None)]*(aux-self.dim), method='highs-ds', options={'time_limit': seconds})
        report = {'Lean_proof': False, 'CQ01Empty_proved': False, 'all_length_certificate_form': True,
            'both_end_distances': True, 'potential_variables': self.dim, 'auxiliary_variables': aux-self.dim,
            'inequalities': len(rows), 'status': int(fit.status), 'message': fit.message}
        if fit.success: report.update(candidate=fit.x.tolist(), exact_rational_check_passed=False,
            maximum_float_residual=float(np.max(matrix@fit.x-np.array(rhs))))
        return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius', type=int, default=3); ap.add_argument('--head-history', type=int, default=8)
    ap.add_argument('--controller-length', type=int, default=7)
    ap.add_argument('--front-parity', type=int, choices=[0, 1], default=0)
    ap.add_argument('--reward', choices=['cycle', 'short-gap', 'long-gap'], default='short-gap')
    ap.add_argument('--seconds', type=int, default=120)
    args = ap.parse_args(); started = time.monotonic()
    fc = finite_row_controls(); model = DistanceModel(args.radius, args.head_history, make_controller(args.controller_length), args.reward, args.front_parity)
    controls = model.controls(); print(json.dumps({'stage': 'controls', **controls}), flush=True)
    report = model.solve(args.seconds)
    report.update(radius=args.radius, head_history=args.head_history, controller_length=args.controller_length,
        front_parity=args.front_parity, reward=args.reward, controls=controls, finite_row_controls=fc,
        seconds=round(time.monotonic()-started, 3))
    path = HERE/f'front-distance-r{args.radius}-head{args.head_history}-memory{args.controller_length}-parity{args.front_parity}-{args.reward}.json'
    path.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'candidate'}))


if __name__ == '__main__': main()
