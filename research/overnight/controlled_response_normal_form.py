"""Falsify completeness of two finite terminal response rewrites.

Exact finite partition refinement on all width-W states of the triangular Q
map. The result is finite evidence, not an unbounded Lean completeness proof.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np


def diagonal(x):
    return x ^ ((x >> 1) | (x >> 2))


def normal_form(x):
    while x.bit_length() >= 3:
        n = x.bit_length()-3
        top = x >> n
        if top == 6:  # physical terminal 011 -> 01
            x = (2 << n) | (x & ((1 << n)-1))
        elif top == 5:  # physical terminal 101 -> 11
            x = (3 << n) | (x & ((1 << n)-1))
        else:
            break
    return x


def check_width(w):
    rows = np.arange(1 << w, dtype=np.int64)
    q = diagonal(rows)
    obs = (rows & 1) + 2*((rows | (rows >> 1)) & 1)
    _, part = np.unique(obs, return_inverse=True)
    count = int(part.max())+1
    history = [count]
    while True:
        # Refine by observation at time 0 and the complete known future class.
        _, newpart = np.unique(obs + 4*part[q], return_inverse=True)
        newcount = int(newpart.max())+1
        history.append(newcount)
        part = newpart
        if count == newcount:
            break
        count = newcount
    normal = np.fromiter((normal_form(int(r)) for r in rows), dtype=np.int64, count=len(rows))
    _, npart = np.unique(normal, return_inverse=True)
    # Both induced maps must be single-valued; class numbering is arbitrary.
    pairs = np.unique(np.stack([part, npart], axis=1), axis=0)
    matches = len(pairs) == int(part.max())+1 == int(npart.max())+1
    qnormal = np.fromiter((normal_form(int(r)) for r in q), dtype=np.int64, count=len(rows))
    normalqnormal = np.fromiter((normal_form(diagonal(int(r))) for r in normal), dtype=np.int64, count=len(rows))
    return {'width': w, 'states': len(rows), 'classes': int(part.max())+1,
        'refinement_class_counts': history, 'normal_form_partition_matches': matches,
        'q_normalizes_consistently': bool(np.array_equal(qnormal, normalqnormal)),
        'predicted_count_matches': int(part.max())+1 == (1 << (w-1))+2 if w >= 2 else True}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-width', type=int, default=18)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = ap.parse_args()
    started = time.monotonic()
    cases = []
    for w in range(1, args.max_width+1):
        case = check_width(w)
        cases.append(case)
        print(json.dumps(case), flush=True)
        if not case['normal_form_partition_matches']:
            break
    report = {'finite_experiment_only': True, 'lean_completeness_proved': False,
        'max_width_requested': args.max_width, 'cases': cases,
        'seconds': round(time.monotonic()-started, 3)}
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
