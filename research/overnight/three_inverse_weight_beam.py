"""Heuristic minimum-weight search in constrained period-three inverse cones.

Beam pruning is incomplete. No lower bound, density theorem or C3w result is
inferred. Every reported row is independently forward checked.
"""

import argparse
import json
from pathlib import Path
import random
from time import perf_counter

from three_inverse_cone_probe import inverse, forward_packed


def prefix_xor(value, bits):
    shift = 1
    while shift < bits:
        value ^= value << shift
        shift *= 2
    return value & ((1 << bits)-1)


def extend(r, previous, k, head):
    source = r | (previous << 1) | int(k > 0 and (k-1) % 3 == 1)
    scan = prefix_xor(source, k)
    return ((scan ^ (((1 << k)-1) if head else 0)) << 1) | head


def controls():
    rng = random.Random(202610240850)
    for length in range(1, 129):
        head = rng.getrandbits(length)
        r = previous = row = 0
        for k in range(length):
            nxt = extend(r, previous, k, (head >> k) & 1)
            row |= ((nxt >> k) & 1) << k
            previous, r = r, nxt
        boundary = sum(int(t % 3 == 1) << t for t in range(length))
        assert inverse(head, boundary, length) == row
        assert forward_packed(row, length) == head
    return 128


def search(depth, beam, output):
    started = perf_counter()
    rng = random.Random(202610240851)
    # Last two anti-diagonals, initial row, head trace, prefix weight.
    states = [(0, 0, 0, 0, 0)]
    report = {'Lean_verified': False, 'heuristic_only': True, 'coverage_complete': False,
              'density_lower_bound_proved': False, 'C3w_proved': False,
              'full_problem_solved': False, 'beam': beam,
              'roundtrip_controls': controls(), 'levels': []}
    for k in range(depth):
        choices = (0, 1) if k % 3 == 0 else (int(k % 3 == 2),)
        candidates = []
        for r, previous, row, trace, weight in states:
            for head in choices:
                nxt = extend(r, previous, k, head)
                bit = (nxt >> k) & 1
                candidates.append((nxt, r, row | (bit << k), trace | (head << k), weight+bit))
        # Equal anti-diagonals have identical possible continuations; retaining
        # the least accumulated weight is sound. Beam truncation is not.
        best = {}
        for candidate in candidates:
            key = candidate[:2]
            if key not in best or candidate[-1] < best[key][-1]:
                best[key] = candidate
        ranked = [(s[-1], rng.random(), s) for s in best.values()]
        ranked.sort(key=lambda s: s[:2])
        states = [s for _, _, s in ranked[:beam]]
        if k % 3 == 2 and (k < 63 or k % 96 == 95 or k+1 == depth):
            winner = states[0]
            assert forward_packed(winner[2], k+1) == winner[3]
            entry = {'depth': k+1, 'best_retained_weight': winner[-1],
                     'four_weight_minus_depth': 4*winner[-1]-(k+1),
                     'five_weight_minus_depth': 5*winner[-1]-(k+1),
                     'retained_states': len(states), 'row': str(winner[2]),
                     'trace': str(winner[3]), 'forward_check_passed': True}
            report['levels'].append(entry)
            report['seconds'] = perf_counter()-started
            output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
            if k >= 63:
                print(json.dumps({a: b for a, b in entry.items() if a not in ('row', 'trace')}), flush=True)
    report['seconds'] = perf_counter()-started
    output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'completed': True, 'depth': depth, 'seconds': report['seconds']}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=1536)
    parser.add_argument('--beam', type=int, default=1024)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    search(args.depth, args.beam, args.output)
