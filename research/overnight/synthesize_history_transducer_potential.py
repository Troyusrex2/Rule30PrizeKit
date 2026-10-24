"""Exact multi-diagonal histories in an all-length graph-potential search.

Numerical exploration only, with no theorem claim. Unlike the earlier ribbon
relaxation, each retained old diagonal obeys its exact recurrence from the two
older retained diagonals. Only the oldest two input columns are free. A
vertical feature records all retained diagonal bits at a common position.
"""
import argparse
from collections import deque
import json
from fractions import Fraction
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from empty_gate_controller import make_controller
from reachable_variation_potential import advance
from synthesize_front_transducer_potential import finite_row_controls
from synthesize_transducer_potential import HERE, add


class HistoryModel:
    def __init__(self, height, history, controller, reward, parity, radius=1):
        if height < 3 or history < 2 or (height+history)%2:
            raise ValueError('Use height>=3 and even height+history')
        if radius not in [1, 2]: raise ValueError('Use radius 1 or 2')
        self.h = height; self.m = history; self.controller = controller; self.parity = parity; self.radius = radius
        self.words = controller['words']; self.length = controller['length']; self.patterns = 1<<(height*radius)
        if self.length < (height+history)//2+1: raise ValueError('Not enough gate history')
        self.lookup = {w: j for j, w in enumerate(self.words)}; self.span = 3*self.patterns
        self.headbase = len(self.words)*self.span; self.dim = self.headbase+len(self.words)
        self.edges = {}; self.cases = []; self.case_lookup = {}
        mask = (1<<self.length)-1
        for word in controller['transition_words']:
            old, new = self.lookup[word&mask], self.lookup[word>>1]
            case = self.make_case(old, new, reward); self.cases.append(case); self.case_lookup[(old, new)] = case

    def index(self, age, group, code): return age*self.span+group*self.patterns+code

    def pattern(self, rows, i):
        code = 0
        for offset in range(self.radius):
            if i >= offset:
                code |= sum(((a>>(i-offset))&1)<<(j+offset*self.h) for j, a in enumerate(rows))
        return code

    def features(self, rows, cut, age, tail=True):
        vec = {self.headbase+age: 1}
        for i in range(cut):
            code = self.pattern(rows, i)
            add(vec, self.index(age, 0, code), 1)
            if i == 0: add(vec, self.index(age, 1, code), 1)
            if i == cut-1 and tail: add(vec, self.index(age, 2, code), 1)
        return vec

    def vertex(self, rows, c, d, scan):
        return tuple((a>>(scan-2))&3 for a in rows)+((c>>(scan-1))&3, (d>>(scan-1))&7)

    def get_edges(self, u):
        if u in self.edges: return self.edges[u]
        # Buffers have their most recent bit in position 1.
        # Older code used the opposite convention; all operations here are
        # independently checked against direct complete diagonal updates.
        recent = [a>>1 for a in u[:self.h]]; older = [a&1 for a in u[:self.h]]
        c, d = u[-2:]; out = []
        for bottom in range(4):
            bits = [0]*self.h; bits[-2:] = [bottom&1, bottom>>1]
            for j in range(self.h-3, -1, -1):
                bits[j] = recent[j]^(recent[j+1]|older[j+2])
            ci = (c>>1)^(bits[0]|recent[1]); di = (d>>2)^(ci|bits[0])
            v = tuple((recent[j]|(bits[j]<<1)) for j in range(self.h))+((c>>1)|(ci<<1), (d>>1)|(di<<2))
            old = sum(bit<<j for j, bit in enumerate(bits))
            new = ((d>>1)&1)|((c>>1)<<1)|sum(bits[j]<<(j+2) for j in range(self.h-2))
            if self.radius == 2:
                old |= sum(bit<<(j+self.h) for j, bit in enumerate(recent))
                newprev = (d&1)|((c&1)<<1)|sum(recent[j]<<(j+2) for j in range(self.h-2))
                new |= newprev<<self.h
            edge = (u, v, old, new, tuple(bits), ci, di)
            out.append(edge)
        self.edges[u] = out
        return out

    def terminal(self, edge):
        u, v, old, new, bits, ci, di = edge; p = self.parity
        if ci != p or di != 0 or u[-1]>>2 != 1: return False
        for j, bit in enumerate(bits):
            delta = (j+1)//2 if p == 0 else j//2
            if bit != int(delta == 0): return False
            # A known edge or its immediate inner neighbor is black. Beyond
            # the front everything is white. All other bits remain free.
            for distance, known in [(1, u[j]>>1), (2, u[j]&1)]:
                if delta > distance and known != 0: return False
                if delta == distance and known != 1: return False
        return True

    def make_case(self, old, new, reward):
        word = self.words[old]; total = self.m+self.h; rows = [0]*self.h
        for cycle in range(total//2):
            g = (word>>(self.length-1-total//2+cycle))&1
            c = advance(rows[0], rows[1], 2*cycle, 1-g); rows = [c]+rows[:-1]
            d = advance(rows[0], rows[1], 2*cycle+1, 1); rows = [d]+rows[:-1]
        c = advance(rows[0], rows[1], total, 1-((word>>(self.length-1))&1))
        d = advance(c, rows[0], total+1, 1); newrows = [d, c]+rows[:-2]
        source = self.features(newrows, self.m, new, False)
        for index, value in self.features(rows, self.m, old, False).items(): add(source, index, -value)
        u = self.vertex(rows, c, d, self.m)
        reached = {u}; reverse = {}; queue = deque([u])
        while queue:
            current = queue.popleft()
            for edge in self.get_edges(current):
                nxt = edge[1]; reverse.setdefault(nxt, []).append(current)
                if nxt not in reached: reached.add(nxt); queue.append(nxt)
        ends = [e for v in reached for e in self.get_edges(v) if self.terminal(e)]
        coreach = {e[0] for e in ends}; queue = deque(coreach)
        while queue:
            for prev in reverse.get(queue.popleft(), []):
                if prev not in coreach: coreach.add(prev); queue.append(prev)
        relevant = reached&coreach
        offset = 3 if reward == 'short-gap' else 5
        amount = int(reward == 'cycle' or ((word>>(self.length-1))&1 and (word>>(self.length-1-offset))&1))
        return {'key': (old, new), 'vertices': relevant, 'ends': [e for e in ends if e[0] in relevant],
                'source': (u, source) if u in relevant else None, 'reward': amount}

    def gain(self, case, edge, terminal=False):
        old, new = case['key']; vec = {}
        add(vec, self.index(old, 0, edge[2]), -1); add(vec, self.index(new, 0, edge[3]), 1)
        if terminal:
            code = 1+2*self.parity
            if self.radius == 2: code |= (edge[3]&((1<<self.h)-1))<<self.h
            add(vec, self.index(new, 0, code), 1)
            add(vec, self.index(new, 2, code), 1); add(vec, self.index(old, 2, edge[2]), -1)
        return vec

    def controls(self, samples=8, depth=257):
        rng = random.Random(20261024); vals, succ = self.controller['core_states'], self.controller['successors']
        checked = 0; edgechecks = 0
        for _ in range(samples):
            q = rng.randrange(len(vals)); bits = []
            for j in range(self.length):
                bits.append(vals[q]&1)
                if j+1 < self.length: q = rng.choice(succ[q])
            word = sum(bit<<j for j, bit in enumerate(bits)); rows = [0]*self.h
            for cycle in range(depth):
                n = 2*cycle; old = self.lookup[word]; nq = rng.choice(succ[q])
                nw = (word>>1)|((vals[nq]&1)<<(self.length-1)); new = self.lookup[nw]
                c = advance(rows[0], rows[1], n, 1-(vals[q]&1)); d = advance(c, rows[0], n+1, 1)
                nr = [d, c]+rows[:-2]; cut = rows[0].bit_length(); case = self.case_lookup[(old, new)]
                if n > self.m+self.h:
                    # Check recurrence even when no finite-front endpoint occurs.
                    for i in [self.m, max(self.m, n//2)]:
                        u = self.vertex(rows, c, d, i)
                        ebits = tuple((a>>i)&1 for a in rows)
                        found = [e for e in self.get_edges(u) if e[4] == ebits]
                        assert len(found) == 1
                        edge = found[0]
                        assert edge[1] == self.vertex(rows, c, d, i+1)
                        assert edge[3] == self.pattern(nr, i)
                        edgechecks += 1
                lengths = [cut-((j+1)//2 if self.parity == 0 else j//2) for j in range(self.h)]
                if (cut > self.m+2 and [a.bit_length() for a in rows] == lengths
                        and c.bit_length() == cut+self.parity and d.bit_length() == cut+1):
                    accum = self.features(nr, self.m, new, False)
                    for index, value in self.features(rows, self.m, old, False).items(): add(accum, index, -value)
                    u = self.vertex(rows, c, d, self.m)
                    assert case['source'] == (u, accum)
                    for i in range(self.m, cut):
                        ebits = tuple((a>>i)&1 for a in rows)
                        edge, = [e for e in self.get_edges(u) if e[4] == ebits]
                        if i == cut-1: assert self.terminal(edge)
                        for index, value in self.gain(case, edge, i == cut-1).items(): add(accum, index, value)
                        u = edge[1]
                    expected = self.features(nr, cut+1, new)
                    for index, value in self.features(rows, cut, old).items(): add(expected, index, -value)
                    assert accum == expected
                    checked += 1
                rows, word, q = nr, nw, nq
        return {'selected_front_words': checked, 'exact_history_edge_checks': edgechecks, 'feature_accounting_passed': True}

    def solve(self, seconds, graph_lower_bound=False, exact_solver=False):
        rows = []; rhs = []; aux = self.dim; counts = []
        for case in self.cases:
            rv = {v: aux+i for i, v in enumerate(sorted(case['vertices']))}; aux += len(rv)
            qv = {}
            if graph_lower_bound:
                qv = {v: aux+i for i, v in enumerate(sorted(case['vertices']))}; aux += len(qv)
            counts.append({'case': case['key'], 'vertices': len(rv), 'terminal_edges': len(case['ends'])})
            if case['source']:
                u, vec = case['source']; row = dict(vec); add(row, rv[u], -1); rows.append(row); rhs.append(-case['reward'])
            for u in rv:
                for edge in self.get_edges(u):
                    v = edge[1]
                    if v not in rv: continue
                    row = self.gain(case, edge); add(row, rv[u], 1); add(row, rv[v], -1); rows.append(row); rhs.append(0)
                    if graph_lower_bound:
                        # old body cost >= Q(v)-Q(u). Telescoping gives a
                        # uniform lower bound because this graph is finite.
                        row = {self.index(case['key'][0], 0, edge[2]): -1}
                        add(row, qv[v], 1); add(row, qv[u], -1); rows.append(row); rhs.append(0)
            for edge in case['ends']:
                row = self.gain(case, edge, True); add(row, rv[edge[0]], 1); rows.append(row); rhs.append(0)
        values = []; indices = []; indptr = [0]
        for row in rows:
            for index, value in row.items(): values.append(value); indices.append(index)
            indptr.append(len(values))
        matrix = csr_matrix((values, indices, indptr), shape=(len(rows), aux), dtype=float)
        if exact_solver:
            import z3
            variables = [z3.Real(f'w{j}') for j in range(aux)]
            solver = z3.Solver(); solver.set(timeout=1000*seconds)
            if not graph_lower_bound:
                solver.add(*[x >= 0 for x in variables[:self.dim]])
            for row, bound in zip(rows, rhs):
                solver.add(z3.Sum([value*variables[index] for index, value in row.items()]) <= bound)
            status = solver.check()
            report = {'Lean_proof': False, 'CQ01Empty_proved': False, 'all_length_certificate_form': True,
                'exact_retained_history': self.h, 'potential_variables': self.dim, 'auxiliary_variables': aux-self.dim,
                'inequalities': len(rows), 'cases': counts, 'solver': 'Z3 rational linear arithmetic',
                'status': str(status), 'signed_weights_with_graph_lower_bound': graph_lower_bound}
            if status == z3.sat:
                model = solver.model()
                rational = []
                for x in variables:
                    v = model.eval(x, model_completion=True)
                    rational.append(Fraction(v.numerator_as_long(), v.denominator_as_long()))
                valid = all(sum(value*rational[index] for index, value in row.items()) <= bound for row, bound in zip(rows, rhs))
                valid &= graph_lower_bound or all(x >= 0 for x in rational[:self.dim])
                report.update(candidate=[str(x) for x in rational], exact_rational_check_passed=bool(valid), kernel_check_passed=False)
            elif status == z3.unknown: report['reason_unknown'] = solver.reason_unknown()
            return report
        objective = np.zeros(aux)
        if not graph_lower_bound: objective[:self.dim] = 1
        fit = linprog(objective, A_ub=matrix, b_ub=rhs,
            bounds=([(None, None)]*aux if graph_lower_bound else
                [(0, None)]*self.dim+[(None, None)]*(aux-self.dim)), method='highs-ds', options={'time_limit': seconds})
        report = {'Lean_proof': False, 'CQ01Empty_proved': False, 'all_length_certificate_form': True,
            'exact_retained_history': self.h, 'potential_variables': self.dim, 'auxiliary_variables': aux-self.dim,
            'inequalities': len(rows), 'cases': counts, 'status': int(fit.status), 'message': fit.message}
        report['signed_weights_with_graph_lower_bound'] = graph_lower_bound
        if fit.success: report.update(candidate=fit.x.tolist(), exact_rational_check_passed=False,
            maximum_float_residual=float(np.max(matrix@fit.x-np.array(rhs))))
        return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--height', type=int, default=4); ap.add_argument('--head-history', type=int, default=8)
    ap.add_argument('--radius', type=int, choices=[1, 2], default=1)
    ap.add_argument('--controller-length', type=int, default=7)
    ap.add_argument('--front-parity', type=int, choices=[0, 1], default=0)
    ap.add_argument('--reward', choices=['cycle', 'short-gap', 'long-gap'], default='short-gap')
    ap.add_argument('--seconds', type=int, default=120)
    ap.add_argument('--graph-lower-bound', action='store_true', help='Permit signed feature weights with a graph certificate of a uniform lower bound')
    ap.add_argument('--exact-solver', action='store_true', help='Use exact Z3 rational linear arithmetic instead of floating HiGHS')
    args = ap.parse_args(); started = time.monotonic(); fc = finite_row_controls()
    model = HistoryModel(args.height, args.head_history, make_controller(args.controller_length), args.reward, args.front_parity, args.radius)
    controls = model.controls(); print(json.dumps({'stage': 'controls', **controls, 'graph_vertices': len(model.edges)}), flush=True)
    report = model.solve(args.seconds, args.graph_lower_bound, args.exact_solver)
    report.update(head_history=args.head_history, controller_length=args.controller_length, front_parity=args.front_parity, radius=args.radius,
        reward=args.reward, controls=controls, finite_row_controls=fc, seconds=round(time.monotonic()-started, 3))
    suffix = '-graph-lower-bound' if args.graph_lower_bound else ''
    if args.exact_solver: suffix += '-exact'
    path = HERE/f'history-transducer-height{args.height}-radius{args.radius}-head{args.head_history}-memory{args.controller_length}-parity{args.front_parity}-{args.reward}{suffix}.json'
    path.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ['candidate', 'cases']}))


if __name__ == '__main__': main()
