"""Falsify free-head variation/initial-weight estimates in C3 inverse cones.

Beam pruning is incomplete. A surviving estimate is not a theorem. A finite
positive score refutes only the specified zero-offset inequality and gives
a lower bound on any offset. Every saved witness is forward checked.
"""

import argparse
import json
from pathlib import Path
import random
from time import perf_counter

from three_inverse_cone_probe import forward_packed
from three_inverse_weight_beam import controls, extend


def search(depth, beam, factor, output):
    started = perf_counter()
    rng = random.Random(202610240907)
    # Two anti-diagonals, initial row, trace, weight, variation, last free bit.
    states = [(0, 0, 0, 0, 0, 0, 0)]
    report = {'Lean_verified': False, 'heuristic_only': True, 'coverage_complete': False,
              'variation_estimate_proved': False, 'C3w_proved': False,
              'full_problem_solved': False, 'factor': factor, 'beam': beam,
              'roundtrip_controls': controls(), 'levels': [], 'largest_required_offset': 0,
              'positive_score_witness': None}

    def checked_witness(s, length):
        r, previous, row, trace, weight, changes, mode = s
        assert forward_packed(row, length) == trace
        free = [(trace >> t) & 1 for t in range(0, length, 3)]
        assert sum(a != b for a, b in zip(free, free[1:])) == changes
        assert row.bit_count() == weight
        return {'depth': length, 'variation': changes, 'black_weight': weight,
                'score': changes-factor*weight, 'row': str(row), 'trace': str(trace),
                'independent_forward_check_passed': True}

    for k in range(depth):
        choices = (0, 1) if k % 3 == 0 else (int(k % 3 == 2),)
        candidates = []
        for r, previous, row, trace, weight, changes, mode in states:
            for head in choices:
                nxt = extend(r, previous, k, head)
                bit = (nxt >> k) & 1
                changed = int(k > 0 and k % 3 == 0 and head != mode)
                next_mode = head if k % 3 == 0 else mode
                candidates.append((nxt, r, row | (bit << k), trace | (head << k),
                                   weight+bit, changes+changed, next_mode))
        best = {}
        for s in candidates:
            key = (s[0], s[1], s[6])
            score = s[5]-factor*s[4]
            if key not in best or score > best[key][0]:
                best[key] = (score, s)
        ranked = [(score, rng.random(), s) for score, s in best.values()]
        ranked.sort(key=lambda s: s[:2], reverse=True)
        states = [s for _, _, s in ranked[:beam]]
        if k % 3 == 2:
            score = ranked[0][0]
            if score > report['largest_required_offset']:
                report['largest_required_offset'] = score
                report['positive_score_witness'] = checked_witness(states[0], k+1)
            if k % 96 == 95 or k+1 == depth:
                witness = checked_witness(states[0], k+1)
                report['levels'].append(witness)
                report['seconds'] = perf_counter()-started
                output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
                print(json.dumps({a: b for a, b in witness.items() if a not in ('row', 'trace')}), flush=True)
    report['seconds'] = perf_counter()-started
    output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'completed': True, 'factor': factor, 'depth': depth,
                      'largest_required_offset': report['largest_required_offset'],
                      'seconds': report['seconds']}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=1536)
    parser.add_argument('--beam', type=int, default=1024)
    parser.add_argument('--factor', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    search(args.depth, args.beam, args.factor, args.output)
