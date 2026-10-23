"""Compute the unique alternating-center candidate for a finite right half.

All outputs are finite observations, not nonperiodicity proofs.  Bit k of the
returned integer is the cell at depth k+1 to the left of the center at time 0.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time


def driven_right_trace(right, horizon, boundary):
    trace = 0
    for t in range(horizon):
        trace |= (right & 1) << t
        right = ((right << 1) | boundary(t)) ^ (right | (right >> 1))
    return trace


def candidate(right, depth):
    # A new column to the left is c(t+1) XOR (c(t) OR r(t)).
    center = sum(1 << t for t in range(0, depth + 1, 2))
    neighbor = driven_right_trace(right, depth + 1, lambda t: 1 - t % 2)
    initial = 0
    mask = (1 << depth) - 1
    for k in range(depth):
        left = ((center >> 1) ^ (center | neighbor)) & mask
        initial |= (left & 1) << k
        neighbor, center = center, left
        mask >>= 1
    return initial


def direct_trace(left, right, steps):
    # Independent full-row evolution: high bits lie to the left.
    width = max(left.bit_length(), right.bit_length())
    row = 1 << width
    for k in range(width):
        row |= ((left >> k) & 1) << (width + k + 1)
        row |= ((right >> k) & 1) << (width - k - 1)
    result = []
    for t in range(steps):
        result.append((row >> (width + t)) & 1)
        row ^= (row << 1) | (row << 2)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=65536)
    args = parser.parse_args()
    started = time.monotonic()
    initial = candidate(0, args.depth)
    bits = ''.join(str((initial >> k) & 1) for k in range(args.depth))
    # Reconstruct shorter cones and compare to independently evolved full rows.
    controls = []
    for r in [0, 1, 2, 3, 5, 13]:
        for n in [1, 2, 3, 8, 31, 64, 127]:
            left = candidate(r, n)
            actual = direct_trace(left, r, n + 1)
            assert actual == [1 - t % 2 for t in range(n + 1)]
            assert left == candidate(r, n + 1) & ((1 << n) - 1)
            controls.append({'right': r, 'depth': n, 'agrees_through': n})
    black = [k + 1 for k, bit in enumerate(bits) if bit == '1']
    gaps = [b - a - 1 for a, b in zip(black, black[1:])]
    report = {'finite_experiment_only': True, 'depth': args.depth,
              'prefix': bits[:256], 'black_count': len(black),
              'last_black_depth': black[-1], 'max_internal_white_run': max(gaps),
              'block_black_counts': [sum(int(b) for b in bits[k:k+1024])
                                     for k in range(0, args.depth, 1024)],
              'bits_sha256': hashlib.sha256(bits.encode()).hexdigest(),
              'controls': controls, 'seconds': round(time.monotonic() - started, 3)}
    target = Path(__file__).parent
    (target / 'empty-right-candidate.bits').write_text(bits + '\n', encoding='ascii')
    (target / 'empty-right-candidate.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in report.items() if k not in ['controls','block_black_counts']}))


if __name__ == '__main__':
    main()
