"""Exact finite truth tables for possible unbounded constrained-row identities.

This is a falsification instrument, not a proof of any infinite identity.
Bit p of a lane integer is free-bit assignment p.
"""
import argparse
import json
from pathlib import Path
import time


def tables(free_bits):
    lanes = 1 << free_bits
    all_bits = (1 << lanes) - 1
    patterns = []
    for j in range(free_bits):
        block = (1 << (1 << j)) - 1
        pattern = block << (1 << j)
        width = 1 << (j + 1)
        while width < lanes:
            pattern |= pattern << width
            width *= 2
        patterns.append(pattern)
    previous, row, initial = [], [], []
    for k in range(2 * free_bits + 1):
        acc = all_bits if k % 2 == 0 else patterns[k // 2]
        out = [acc]
        for j, a in enumerate(row):
            b = previous[j - 1] if j > 0 else 0
            acc ^= a | b
            out.append(acc)
        initial.append(out[-1])
        previous, row = row, out
    return initial, all_bits, patterns


def direct(initial, steps):
    result = []
    for t in range(steps):
        result.append(initial & 1)
        initial = (initial >> 1) ^ (initial | (initial << 1))
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--free-bits', type=int, default=16)
    args = ap.parse_args()
    started = time.monotonic()
    rows, all_bits, patterns = tables(args.free_bits)
    # Cross-check with an independent ordinary packed forward evolution.
    for assignment in list(range(64)) + [(1 << args.free_bits) - 1]:
        initial = sum(((v >> assignment) & 1) << k for k, v in enumerate(rows))
        observed = direct(initial, len(rows))
        expected = [1 if k % 2 == 0 else (assignment >> (k // 2)) & 1
                    for k in range(len(rows))]
        assert observed == expected
    report = {'finite_truth_tables_only': True, 'free_bits': args.free_bits,
              'depth': len(rows), 'constant_depths': [], 'equalities': [],
              'complement_pairs': [], 'single_variable_functions': []}
    for j, a in enumerate(rows):
        if a in (0, all_bits):
            report['constant_depths'].append([j + 1, int(a == all_bits)])
        for i, p in enumerate(patterns):
            if a == p or a == (p ^ all_bits):
                report['single_variable_functions'].append([j + 1, i, a != p])
        for i, b in enumerate(rows[:j]):
            if a == b:
                report['equalities'].append([i + 1, j + 1])
            if a ^ b == all_bits:
                report['complement_pairs'].append([i + 1, j + 1])
    report['seconds'] = round(time.monotonic() - started, 3)
    (Path(__file__).parent / 'forced-row-identities.json').write_text(
        json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
