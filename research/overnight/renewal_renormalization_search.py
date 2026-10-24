"""Finite falsification of fixed-depth support-descending renewal returns.

Only candidates surviving every sampled gate are reported. A survivor would
still need a universal proof; an empty intersection only refutes this bounded
fixed-depth search, not every possible renormalization.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import random

HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('probe', HERE / 'spacing35_row_probe.py')
probe = importlib.util.module_from_spec(sp)
sp.loader.exec_module(probe)


def candidates(gaps, depth, cycles):
    horizon = 2 * cycles + depth + 2
    g = probe.gate_bits(gaps, (horizon + 1) // 2)
    current = sum(1 << t for t in range(horizon) if t % 2 or not ((g >> (t // 2)) & 1))
    old, result = 0, []
    for k in range(1, depth + 1):
        next_column = (current >> 1) ^ (current | old)
        gate = [1 - ((current >> (2 * r)) & 1) for r in range(cycles + 1)]
        canonical = all((current >> (2 * r + 1)) & 1 and
                        ((next_column >> (2 * r)) & 1) == gate[r] and
                        ((next_column >> (2 * r + 1)) & 1) == gate[r + 1]
                        for r in range(cycles))
        positions = [r for r, b in enumerate(gate) if b]
        renewal = bool(positions) and positions[0] < 5 and positions[-1] >= cycles - 4
        distances = [b - a for a, b in zip(positions, positions[1:])]
        renewal = renewal and all(d in (3, 5) for d in distances)
        isolated = renewal and all(not (a == b == 3) for a, b in zip(distances, distances[1:]))
        if canonical and isolated:
            result.append(k)
        old, current = current, next_column
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth', type=int, default=256)
    ap.add_argument('--samples', type=int, default=48)
    args = ap.parse_args()
    rng = random.Random(20261024)
    gates = [[5], [3, 5], [3, 5, 5], [3, 5, 5, 5]]
    for _ in range(args.samples):
        gaps = []
        for j in range(16):
            gaps.append(5 if gaps and gaps[-1] == 3 else rng.choice([3, 5]))
        gaps[-1] = 5
        gates.append(gaps)
    common = set(range(2, args.depth + 1))
    rows = []
    for gaps in gates:
        found = candidates(gaps, args.depth, 64)
        common.intersection_update(found)
        rows.append({'periodic_gate_gaps': gaps, 'candidate_depths': found})
    report = {'finite_experiments_only': True, 'universal_identity_claim': False,
              'max_depth': args.depth, 'cycles_checked': 64,
              'common_candidate_depths': sorted(common), 'gates': rows}
    (HERE / 'renewal-renormalization-search.json').write_text(json.dumps(report, indent=2) + '\n',
                                                            encoding='utf-8', newline='\n')
    print(json.dumps({'common_candidate_depths': sorted(common), 'gates': len(gates),
                      'max_depth': args.depth}))


if __name__ == '__main__':
    main()
