"""Nonlocal prefix-automaton rank synthesis for the actual zero-boundary map.

Experimental only. A hypothetical finite InX row must first deviate from the
fixed stripe at an even depth: an odd first deviation reaches the wall at an
even time and turns it white. Both the old and new rows retain this necessary
whole-word restriction. This script does not assert a Lean proof of a ranking.
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
        if not row[index]: del row[index]


def scalar_z(row):
    return (row >> 1) ^ (row | (row << 1))


class Model:
    def __init__(self, radius, ones_parity=False, spatial_base=Fraction(1)):
        self.r = radius
        self.size = radius+4
        self.mask = (1 << (self.size-1))-1
        self.patterns = 1 << radius
        self.parity = ones_parity
        self.base = Fraction(spatial_base)
        assert self.base >= 1
        self.states = 12 if ones_parity else 6
        self.dim = self.states*self.patterns
        self.sources = set()
        for bits in range(1 << (radius+1)):
            if not bits & 1: continue
            if radius >= 2 and ((bits >> 1) ^ (bits >> 2)) & 1 != 1: continue
            self.sources.add((bits << 2, 0, 0, True))
        reached = set(self.sources); queue = deque(reached)
        self.edges = {}; reverse = {}
        while queue:
            u = queue.popleft()
            buf, oldstate, newstate, first = u
            out = []
            for bit in [0, 1]:
                full = buf | (bit << (self.size-1))
                old = (full >> 2) & (self.patterns-1)
                new = 0
                for j in range(radius):
                    a, b, c, d, e = [(full >> (j+k)) & 1 for k in range(5)]
                    left = 0 if first and j == 0 else c ^ (b | a)
                    middle = d ^ (c | b)
                    right = e ^ (d | c)
                    new |= (right ^ (middle | left)) << j
                if first and (old & 1 != 1 or new & 1 != 1): continue
                v = (full >> 1, self.advance(oldstate, old & 1),
                     self.advance(newstate, new & 1), False)
                if self.mode(v[1]) == 1 or self.mode(v[2]) == 1: continue
                edge = (u, v, old, new, bit, first)
                out.append(edge)
                reverse.setdefault(v, []).append(u)
                if v not in reached:
                    reached.add(v); queue.append(v)
            self.edges[u] = out
        self.ends = {u for u in reached if u[0] == 0 and not u[3]
                     and self.mode(u[1]) == self.mode(u[2]) == 2}
        coreach = set(self.ends); queue = deque(coreach)
        while queue:
            for u in reverse.get(queue.popleft(), []):
                if u not in coreach:
                    coreach.add(u); queue.append(u)
        self.vertices = reached & coreach
        self.sources &= self.vertices
        assert self.sources and self.ends

    def mode(self, state):
        return (state // (2 if self.parity else 1)) % 3

    def advance(self, state, bit):
        parity = state % 2 if self.parity else 0
        core = state // 2 if self.parity else state
        phase, mode = divmod(core, 3)
        if mode == 0 and bit != 1-phase:
            mode = 1 if phase == 0 else 2
        core = (1-phase)*3+mode
        return 2*core+(parity ^ bit) if self.parity else core

    def index(self, state, pattern):
        return state*self.patterns+pattern

    def gain(self, edge, old_only=False):
        u, _, old, new, _, _ = edge
        result = {}
        if old: add(result, self.index(u[1], old), -1)
        if new and not old_only: add(result, self.index(u[2], new), 1)
        return result

    def features(self, row):
        result = {}; state = 0
        for k in range(row.bit_length()):
            pattern = (row >> k) & (self.patterns-1)
            if pattern: add(result, self.index(state, pattern), self.base**k)
            state = self.advance(state, (row >> k) & 1)
        return result

    def final_mode(self, row):
        state = 0
        for k in range(row.bit_length()+4):
            state = self.advance(state, (row >> k) & 1)
        return self.mode(state)

    def controls(self, count=128):
        rng = random.Random(20261024); accepted = 0
        for _ in range(100000):
            width = rng.randrange(4, 20)
            row = rng.getrandbits(width) | (1 << (width-1)) | 1
            new = scalar_z(scalar_z(row))
            if not new & 1 or self.final_mode(row) != 2 or self.final_mode(new) != 2:
                continue
            u = ((row & ((1 << (self.r+1))-1)) << 2, 0, 0, True)
            assert u in self.sources
            accum = {}; reward = flips = 0
            for k in range(width+self.size+4):
                bit = (row >> (k+self.r+1)) & 1
                edge, = [e for e in self.edges[u] if e[4] == bit]
                assert edge[1] in self.vertices
                for j, v in self.gain(edge).items(): add(accum, j, v*self.base**k)
                reward += int(edge[5]); u = edge[1]
                if self.r >= 2:
                    flips += int(edge[5] and ((edge[2] >> 1) & 1) != ((edge[3] >> 1) & 1))
            assert u in self.ends and reward == 1
            expected = self.features(new)
            for j, v in self.features(row).items(): add(expected, j, -v)
            assert accum == expected
            if self.r >= 2:
                assert flips == int((scalar_z(row) & 1) != (scalar_z(new) & 1))
            accepted += 1
            if accepted == count: break
        assert accepted == count
        return {'independent_integer_double_updates': accepted,
                'exact_nonlocal_feature_accounting_passed': True,
                'odd_time_boundary_flip_accounting_passed': self.r >= 2}

    def solve(self, signed=False, seconds=60, reward_mode='step'):
        assert reward_mode in ['step', 'free-flip']
        assert reward_mode != 'free-flip' or self.r >= 2
        rv = {u: self.dim+i for i, u in enumerate(sorted(self.vertices))}
        offset = self.dim+len(rv)
        qv = {u: offset+i for i, u in enumerate(sorted(self.vertices))} if signed else {}
        dim = offset+len(qv)
        rows, rhs = [], []

        def constraint(cost, u, v, potential, reward=0):
            row = dict(cost)
            add(row, potential[u], 1); add(row, potential[v], -self.base)
            rows.append(row); rhs.append(-reward)

        for s in self.sources:
            rows.append({rv[s]: -1}); rhs.append(0)
            if signed: rows.append({qv[s]: -1}); rhs.append(0)
        for u in self.vertices:
            for edge in self.edges[u]:
                v = edge[1]
                if v not in self.vertices: continue
                reward = int(edge[5])
                if reward_mode == 'free-flip':
                    reward *= int(((edge[2] >> 1) & 1) != ((edge[3] >> 1) & 1))
                constraint(self.gain(edge), u, v, rv, reward)
                if signed: constraint(self.gain(edge, old_only=True), u, v, qv)
        for e in self.ends:
            rows.append({rv[e]: 1}); rhs.append(0)
            if signed: rows.append({qv[e]: 1}); rhs.append(0)
        values, indices, indptr = [], [], [0]
        for row in rows:
            for j, v in row.items(): indices.append(j); values.append(v)
            indptr.append(len(values))
        matrix = csr_matrix((values, indices, indptr), shape=(len(rows), dim), dtype=float)
        bounds = [(None, None)]*dim if signed else [(0, None)]*self.dim+[(None, None)]*(dim-self.dim)
        for state in range(self.states): bounds[self.index(state, 0)] = (0, 0)
        objective = np.zeros(dim)
        if not signed: objective[:self.dim] = 1
        fit = linprog(objective, A_ub=matrix, b_ub=rhs, bounds=bounds, method='highs-ds',
                      options={'time_limit': seconds})
        result = {'unverified_synthesis_only': True, 'Lean_verified': False,
            'Q01_proved': False, 'prize_problem_proved': False,
            'prefix_dfa_states': self.states, 'tracks_prefix_ones_parity': self.parity,
            'pattern_length': self.r, 'signed_weights_with_accepted_path_lower_bound': signed,
            'reward_mode': reward_mode,
            'spatial_geometric_base': str(self.base),
            'first_stripe_deviation_even_at_both_endpoints': True,
            'graph_vertices': len(rv), 'potential_variables': self.dim, 'variables': dim,
            'inequalities': len(rows), 'status': int(fit.status), 'message': fit.message}
        if fit.success:
            rational = [Fraction(float(x)).limit_denominator(100000) for x in fit.x]
            exact = all(sum(v*rational[j] for j, v in row.items()) <= bound
                        for row, bound in zip(rows, rhs))
            exact &= signed or all(x >= 0 for x in rational[:self.dim])
            exact &= all(rational[self.index(state, 0)] == 0 for state in range(self.states))
            result.update(candidate=[str(x) for x in rational], exact_rational_inequalities_passed=bool(exact),
                          kernel_certificate_verified=False)
        return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius', type=int, default=2)
    ap.add_argument('--ones-parity', action='store_true')
    ap.add_argument('--signed', action='store_true')
    ap.add_argument('--reward', choices=['step', 'free-flip'], default='step')
    ap.add_argument('--spatial-base', type=Fraction, default=Fraction(1))
    ap.add_argument('--seconds', type=float, default=60)
    args = ap.parse_args()
    started = time.monotonic()
    model = Model(args.radius, args.ones_parity, args.spatial_base)
    controls = model.controls()
    result = model.solve(args.signed, args.seconds, args.reward)
    result.update(controls=controls, seconds=round(time.monotonic()-started, 3))
    tag = ('-parity' if args.ones_parity else '')+('-signed' if args.signed else '')
    if args.reward != 'step': tag += '-'+args.reward
    if args.spatial_base != 1: tag += '-base'+str(args.spatial_base).replace('/', '_')
    path = Path(__file__).with_name(f'stripe-prefix-dfa-r{args.radius}{tag}.json')
    path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'candidate'}))


if __name__ == '__main__':
    main()
