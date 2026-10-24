"""Test finite-state descriptions of the constrained inverse encoder.

Input symbols are the free head bits at times 3*n; output symbols are the
initial row's consecutive three-cell blocks. Distinct finite continuation
functions give an exact finite lower bound on the number of Mealy states.
No finite experiment proves unbounded state complexity or C3w.
"""

import argparse
import json
from pathlib import Path
import random
from time import perf_counter

from three_inverse_cone_probe import inverse, forward_scalar


def profiles(modes, symbols):
    n = 3*symbols
    boundary = sum(1 << t for t in range(n) if t % 3 == 1)
    head = sum(1 << t for t in range(n) if t % 3 == 2)
    head |= sum(((modes >> j) & 1) << (3*j) for j in range(symbols))
    return head, boundary


def controls():
    rng = random.Random(202610241050)
    for _ in range(64):
        symbols = rng.randrange(1, 33)
        modes = rng.getrandbits(symbols)
        head, boundary = profiles(modes, symbols)
        row = inverse(head, boundary, 3*symbols)
        assert forward_scalar(row, 3*symbols) == head
        prefix = rng.randrange(symbols+1)
        h, c = profiles(modes % (1 << prefix), prefix)
        assert row % (1 << (3*prefix)) == inverse(h, c, 3*prefix)
    return {'independent_forward_checks': 64, 'causal_prefix_checks': 64,
            'AllPassed': True}


def run(symbols, lengths, output):
    began = perf_counter()
    assert 1 <= symbols <= 20 and all(1 <= k <= symbols for k in lengths)
    report = {'Lean_verified': False, 'full_problem_solved': False,
              'C3w_proved': False, 'finite_encoder_proved': False,
              'symbols': symbols, 'controls': controls(), 'results': []}
    codes = [0]*(1 << symbols)
    head, boundary = profiles(0, symbols)
    gray = 0
    for i in range(1 << symbols):
        if i:
            changed = (i & -i).bit_length()-1
            gray ^= 1 << changed
            head ^= 1 << (3*changed)
        if i < 128:
            assert head == profiles(gray, symbols)[0]
        codes[gray] = inverse(head, boundary, 3*symbols)
    report['all_input_words_enumerated'] = len(codes)
    for length in lengths:
        mask = (1 << (3*length))-1
        levels = []
        for depth in range(symbols-length+1):
            groups = {}
            witnesses = []
            for prefix in range(1 << depth):
                signature = tuple((codes[prefix | (v << depth)] >> (3*depth)) & mask
                                  for v in range(1 << length))
                if signature not in groups:
                    groups[signature] = prefix
                    if len(witnesses) < 16:
                        witnesses.append(prefix)
            levels.append({'prefix_symbols': depth, 'distinct_continuation_functions': len(groups),
                           'prefixes': 1 << depth, 'representative_prefixes_first_16': witnesses})
        result = {'continuation_symbols': length, 'levels': levels}
        report['results'].append(result)
        print(json.dumps({'continuation_symbols': length,
                          'state_lower_bounds_by_prefix_depth': [r['distinct_continuation_functions'] for r in levels]}), flush=True)
    report['seconds'] = perf_counter()-began
    output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--symbols', type=int, default=16)
    parser.add_argument('--continuations', nargs='+', type=int, default=[1, 2, 3, 4])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(args.symbols, args.continuations, args.output)
