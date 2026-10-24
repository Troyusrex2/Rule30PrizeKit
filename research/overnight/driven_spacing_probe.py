"""Finite falsification of a candidate eventual spacing constraint on the right.

The constrained input is 1,0,1,0,...; output is column 1 at white steps.
No all-time or all-start claim is made. Exact ordinary integer evolution is
cross-checked on small cones against independent cell-by-cell updates.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import random
import time


def output(start, cycles):
    row, bits = start, []
    for t in range(2 * cycles):
        if t % 2:
            bits.append(row & 1)
        row = ((row << 1) | (1 - t % 2)) ^ (row | (row >> 1))
    return bits


def check_scalar(start, cycles):
    width = max(start.bit_length(), 1) + 2 * cycles + 2
    row = [(start >> j) & 1 for j in range(width)]
    observed = []
    for t in range(2 * cycles):
        if t % 2:
            observed.append(row[0])
        row = [(row[j - 1] if j else 1 - t % 2) ^ (row[j] | row[j + 1])
               for j in range(len(row) - 1)]
    assert observed == output(start, cycles)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--samples', type=int, default=128)
    ap.add_argument('--cycles', type=int, default=16384)
    args = ap.parse_args()
    began = time.monotonic()
    for start in range(32):
        check_scalar(start, 32)
    rng = random.Random(20261024)
    starts = list(range(32)) + [rng.getrandbits(16 + j % 8 * 32)
                                for j in range(args.samples)]
    report = {'finite_experiment_only': True, 'seed': 20261024,
              'cycles': args.cycles, 'scalar_controls': 32, 'starts': []}
    target = Path(__file__).parent / 'driven-spacing-probe.json'
    for start in starts:
        bits = output(start, args.cycles)
        positions = [j for j, bit in enumerate(bits) if bit]
        gaps = [(a, b - a) for a, b in zip(positions, positions[1:])]
        bad = [(a, gap) for a, gap in gaps if gap not in (3, 5)]
        result = {'start': start, 'width': start.bit_length(),
                  'last_observed_bad_gap': bad[-1] if bad else None,
                  'tail_gap_counts': dict(collections.Counter(gap for a, gap in gaps
                                                              if a >= args.cycles // 2)),
                  'output_sha256': hashlib.sha256(bytes(bits)).hexdigest()}
        report['starts'].append(result)
        if len(report['starts']) % 16 == 0:
            target.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
            print(json.dumps({'samples_completed': len(report['starts']),
                              'latest': result}), flush=True)
    report['seconds'] = round(time.monotonic() - began, 3)
    target.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
