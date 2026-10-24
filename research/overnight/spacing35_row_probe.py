"""Falsify a proposed uniform white-gap bound for spacing-three/five gates.

Gates are periodic repeats of a finite list of gaps in {3,5}, so their global
spacing constraint is exact. The reconstructed row is inspected only to a
finite depth. No actual driven-right realizability is assumed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import time


def gate_bits(gaps, horizon):
    period = sum(gaps)
    positions = [0]
    for gap in gaps[:-1]:
        positions.append(positions[-1] + gap)
    return sum(1 << t for t in range(horizon) if t % period in positions)


def initial_row(gaps, depth):
    g = gate_bits(gaps, (depth + 1) // 2)
    current = sum(1 << t for t in range(depth) if t % 2 or not ((g >> (t // 2)) & 1))
    old, row, mask = 0, 0, (1 << depth) - 1
    for k in range(depth):
        row |= (current & 1) << k
        nxt = ((current >> 1) ^ (current | old)) & (mask >> 1)
        old, current = current, nxt
        mask >>= 1
    return row


def check_forward(gaps, row, depth):
    period = sum(gaps)
    positions = [0]
    for gap in gaps[:-1]:
        positions.append(positions[-1] + gap)
    for t in range(depth):
        expected = 1 if t % 2 else int(t // 2 % period not in positions)
        assert row & 1 == expected
        row = (row >> 1) ^ (row | (row << 1))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--samples', type=int, default=256)
    ap.add_argument('--depth', type=int, default=4096)
    ap.add_argument('--isolated-three', action='store_true')
    args = ap.parse_args()
    rng = random.Random(20261024)
    began = time.monotonic()
    best = None
    report = {'finite_observations_only': True, 'right_realizability_claim': False,
              'seed': 20261024, 'depth': args.depth, 'samples': args.samples,
              'isolated_three': args.isolated_three, 'witness': None}
    target = Path(__file__).parent / ('isolated-three-row-probe.json' if args.isolated_three
                                     else 'spacing35-row-probe.json')
    for sample in range(args.samples):
        gaps = []
        for _ in range(32):
            gaps.append(5 if args.isolated_three and gaps and gaps[-1] == 3
                        else rng.choice([3, 5]))
        if args.isolated_three:
            gaps[-1] = 5
        row = initial_row(gaps, args.depth)
        check_forward(gaps, row, args.depth)
        bits = ''.join(str((row >> k) & 1) for k in range(args.depth))
        black = [k for k, b in enumerate(bits) if b == '1']
        length, start = max(((b - a - 1, a + 1) for a, b in zip(black, black[1:])),
                            default=(0, 0))
        if best is None or length > best:
            best = length
            report['witness'] = {'sample': sample, 'periodic_gate_gaps': gaps,
                                 'gate_period': sum(gaps), 'white_run_length': length,
                                 'first_white_depth': start + 1,
                                 'initial_prefix': bits[:start + length + 1],
                                 'row_sha256': hashlib.sha256(bits.encode()).hexdigest(),
                                 'forward_checked': True}
            target.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
            print(json.dumps({k: v for k, v in report['witness'].items()
                              if k != 'initial_prefix'}), flush=True)
    report['seconds'] = round(time.monotonic() - began, 3)
    target.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
