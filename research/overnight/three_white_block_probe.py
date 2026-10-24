"""Exact finite diagnostics for the period-three inverse code.

A white block means three consecutive zero bits of the initial spatial row.
Internal changes count only transitions between modes indexed inside that
block run. A finite maximum is not a uniform bound or a Lean theorem.
"""

import argparse
import json
from pathlib import Path
from time import perf_counter

from three_inverse_cone_probe import inverse, forward_scalar, forward_packed
from three_inverse_mealy_probe import profiles, controls


def measurements(modes, row, symbols):
    run_start = None
    internal_changes = 0
    maximum = 0
    best_run = None
    nonzero_blocks = 0
    variation = 0
    for j in range(symbols):
        changed = j > 0 and ((modes >> j) & 1) != ((modes >> (j-1)) & 1)
        variation += changed
        if (row >> (3*j)) & 7:
            nonzero_blocks += 1
            run_start = None
            internal_changes = 0
        else:
            if run_start is None:
                run_start = j
            else:
                internal_changes += changed
            if internal_changes > maximum:
                maximum = internal_changes
                best_run = [run_start, j]
    return maximum, best_run, variation, nonzero_blocks


def run(symbols, output):
    assert 1 <= symbols <= 20
    began = perf_counter()
    report = {'Lean_verified': False, 'full_problem_solved': False,
              'C3w_proved': False, 'uniform_variation_bound_proved': False,
              'input_symbols': symbols, 'input_words': 1 << symbols,
              'controls': controls(), 'max_internal_white_run_changes': -1,
              'white_run_witness': None,
              'max_variation_minus_twice_nonzero_blocks': -10**9,
              'score_witness': None}
    head, boundary = profiles(0, symbols)
    gray = 0
    for i in range(1 << symbols):
        if i:
            changed = (i & -i).bit_length()-1
            gray ^= 1 << changed
            head ^= 1 << (3*changed)
        row = inverse(head, boundary, 3*symbols)
        changes, interval, variation, nonzero = measurements(gray, row, symbols)
        if changes > report['max_internal_white_run_changes']:
            report['max_internal_white_run_changes'] = changes
            report['white_run_witness'] = dict(modes=str(gray), row=str(row),
                                               interval=interval, changes=changes)
        score = variation-2*nonzero
        if score > report['max_variation_minus_twice_nonzero_blocks']:
            report['max_variation_minus_twice_nonzero_blocks'] = score
            report['score_witness'] = dict(modes=str(gray), row=str(row),
                variation=variation, nonzero_blocks=nonzero, score=score)
    for witness in (report['white_run_witness'], report['score_witness']):
        row = int(witness['row'])
        head, _ = profiles(int(witness['modes']), symbols)
        assert forward_scalar(row, 3*symbols) == head == forward_packed(row, 3*symbols)
        witness['scalar_and_packed_forward_checks_passed'] = True
    report['seconds'] = perf_counter()-began
    output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--symbols', type=int, default=16)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(args.symbols, args.output)
