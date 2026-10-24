"""Synthesis with an exact finite-row wavefront instead of a white suffix.

Exploratory, not Lean verified. Under a hypothetical finite reconstructed row
of outermost black depth W, compare the even diagonals cut at their moving
fronts. The cut grows by one per two reconstruction steps. Endpoint motifs
are checked against independently evolved finite rows below. This avoids
counting the increasingly long zero padding used by the earlier models.
"""
import argparse
import json
import random
import time

from empty_gate_controller import make_controller
from reachable_variation_potential import advance
from synthesize_controlled_cycle_potential import ControlledModel
from synthesize_transducer_potential import HERE, add


class FrontModel(ControlledModel):
    def __init__(self, radius, history, controller, reward, front_parity):
        self.front_parity = front_parity
        super().__init__(radius, history, controller, reward)

    def terminal(self, edge, phase):
        u, v, old, new, ai, bi, ci, di = edge
        # For even W the new C has ended and the new D ends one slot later.
        # For odd W, C and D both end one slot later; old A and B end together.
        if self.front_parity == 0:
            return ai == 1 and bi == ci == di == 0 and u[1]&1 == u[2]&1 == u[3]&1 == 1
        return ai == bi == ci == 1 and di == 0 and u[2]&1 == 0 and u[3]&1 == 1

    def full_vector(self, a, b, length, phase, age):
        vec = self.prefix_vector(a, b, length, phase, age)
        i = length-self.r+1
        code = ((a>>i)&((1<<(self.r-1))-1)) | (((b>>i)&((1<<(self.r-2))-1))<<(self.r-1))
        add(vec, self.index(0, age, 2, code), 1)
        return vec

    def gain(self, case, edge, terminal=False):
        old, new = edge[2:4]
        oldage, newage = case['key'][1], case['nextage']
        vec = {self.index(0, oldage, 0, old): -1}
        # The last generated window ends one beyond the new moving cut.
        if not terminal: add(vec, self.index(0, newage, 0, new), 1)
        else:
            small = (1<<(self.r-1))-1; lower = (1<<(self.r-2))-1
            oldtail = ((old>>1)&small) | (((old>>(self.r+1))&lower)<<(self.r-1))
            newtail = (new&small) | (((new>>self.r)&lower)<<(self.r-1))
            add(vec, self.index(0, oldage, 2, oldtail), -1)
            add(vec, self.index(0, newage, 2, newtail), 1)
        return vec

    def controls(self, samples=12, depth=385):
        rng = random.Random(20261024)
        vals, succ = self.controller['core_states'], self.controller['successors']
        checked = 0
        for _ in range(samples):
            q = rng.randrange(len(vals)); bits = []
            for j in range(self.length):
                bits.append(vals[q]&1)
                if j+1 < self.length: q = rng.choice(succ[q])
            word = sum(bit<<j for j, bit in enumerate(bits)); a = b = 0
            for cycle in range(depth):
                n = 2*cycle; old = self.lookup[word]
                nq = rng.choice(succ[q]); nw = (word>>1)|((vals[nq]&1)<<(self.length-1))
                new = self.lookup[nw]; case = self.case_lookup[(old, new)]
                c = advance(a, b, n, 1-(vals[q]&1)); d = advance(c, a, n+1, 1)
                k = a.bit_length()
                if (k > self.history and b.bit_length() == k-1+self.front_parity and
                        c.bit_length() == k+self.front_parity and d.bit_length() == k+1):
                    m = self.history
                    accum = self.prefix_vector(d&((1<<(m+2))-1), c&((1<<(m+1))-1), m+2, 0, new)
                    for j, value in self.prefix_vector(a&((1<<m)-1), b&((1<<(m-1))-1), m, 0, old).items():
                        add(accum, j, -value)
                    u = self.vertex(a, b, c, d, m)
                    assert any(u == v and accum == vec for v, vec in case['sources'])
                    for i in range(m, k):
                        data = ((a>>i)&1, (b>>i)&1, (c>>(i+1))&1, (d>>(i+2))&1)
                        edge, = [e for e in self.edges[u] if e[4:] == data]
                        if i == k-1: assert self.terminal(edge, 0)
                        for j, value in self.gain(case, edge, i == k-1).items(): add(accum, j, value)
                        u = edge[1]
                    expected = self.full_vector(d, c, k+1, 0, new)
                    for j, value in self.full_vector(a, b, k, 0, old).items(): add(expected, j, -value)
                    assert accum == expected
                    checked += 1
                a, b, word, q = d, c, nw, nq
        return {'selected_actual_words': checked, 'moving_cut_feature_accounting_passed': True}


def finite_row_controls():
    # Cellwise zero-boundary evolution, independent of packed reconstruction.
    rng = random.Random(20261024); checked = 0
    for width in range(1, 25):
        for _ in range(3):
            row = [0]+[rng.randrange(2) for _ in range(width-1)]+[1]
            rows = [row]
            for t in range(110):
                old = row+[0, 0]
                row = [0]+[old[k+1]^(old[k]|old[k-1]) for k in range(1, len(old)-1)]
                rows.append(row)
            def diag(n):
                return sum((rows[n-1-i][i+1] if i+1 < len(rows[n-1-i]) else 0)<<i for i in range(n))
            for n in range(2*width+8, 100, 2):
                a, b, c, d = diag(n), diag(n-1), diag(n+1), diag(n+2)
                k = a.bit_length()
                assert k == (n+width)//2
                assert b.bit_length() == k-1+width%2
                assert c.bit_length() == k+width%2 and d.bit_length() == k+1
                assert (d>>k)&1 == 1 and (d>>(k+1)) == 0
                if width%2 == 0:
                    assert (b>>(k-2))&1 == (c>>(k-1))&1 == 1
                    assert (b>>(k-1)) == (c>>k) == 0
                else:
                    assert (b>>(k-1))&1 == (c>>k)&1 == 1
                    assert (c>>(k-1))&1 == 0
                checked += 1
    return {'independent_cellwise_finite_row_cases': checked, 'endpoint_motifs_passed': True}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--head-history', type=int, default=8)
    ap.add_argument('--controller-length', type=int, default=7)
    ap.add_argument('--front-parity', type=int, choices=[0, 1], default=0)
    ap.add_argument('--reward', choices=['cycle', 'short-gap', 'long-gap'], default='short-gap')
    ap.add_argument('--seconds', type=int, default=120)
    ap.add_argument('--farkas', action='store_true')
    args = ap.parse_args(); started = time.monotonic()
    row_controls = finite_row_controls(); print(json.dumps({'stage': 'finite_row_controls', **row_controls}), flush=True)
    model = FrontModel(args.radius, args.head_history, make_controller(args.controller_length), args.reward, args.front_parity)
    controls = model.controls(); print(json.dumps({'stage': 'feature_controls', **controls}), flush=True)
    report = model.solve(args.seconds)
    if args.farkas and report['status'] == 2: report['farkas'] = model.farkas(args.seconds)
    report.update(front_parity=args.front_parity, controller_length=args.controller_length,
        reward=args.reward, controls=controls, finite_row_controls=row_controls,
        seconds=round(time.monotonic()-started, 3))
    report.pop('white_suffix', None)
    report['moving_front_cut'] = True
    report['tail_feature_radius'] = args.radius-1
    target = HERE/f'front-transducer-r{args.radius}-head{args.head_history}-memory{args.controller_length}-parity{args.front_parity}-{args.reward}.json'
    target.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ['cases', 'candidate', 'farkas']}))


if __name__ == '__main__': main()
