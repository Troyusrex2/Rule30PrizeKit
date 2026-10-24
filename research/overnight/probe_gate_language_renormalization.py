"""Finite symbolic falsification of a fixed-depth gate-language return.

Enumerate words in the eight-bit gate SFT, reconstruct temporal columns, and
look for a column with all odd entries black whose recoded free gate again
has the same eight-bit language. This is an experiment, not a Lean theorem.
"""
import argparse
import json
from pathlib import Path

ALLOWED = {8, 9, 16, 18, 33, 36, 66, 72, 132, 144}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--gate-bits', type=int, default=48)
    ap.add_argument('--word-guard', type=int, default=100000)
    args = ap.parse_args(); h = args.gate_bits
    if h < 16: raise ValueError('Use at least 16 gate bits')
    words = {w&127 for w in ALLOWED}; counts = {7: len(words)}
    for n in range(7, h):
        words = {w|(bit<<n) for w in words for bit in [0, 1]
                 if (w>>(n-7))|(bit<<7) in ALLOWED}
        counts[n+1] = len(words)
        if len(words) > args.word_guard: raise RuntimeError('Finite word guard reached; no search conclusion')
    ordered = sorted(words); columns = []
    for word in ordered:
        boundary = sum((1-((word>>r)&1))<<(2*r) for r in range(h))
        boundary |= sum(1<<(2*r+1) for r in range(h))
        assert all((word>>r)&255 in ALLOWED for r in range(h-7))
        columns.append([0, boundary])
    mask = (1<<(2*h))-1; constants = []; failures = []
    for depth in range(1, 2*h-16):
        odd = {(b>>1)&1 for a, b in columns}; even = {b&1 for a, b in columns}
        if len(odd) == 1:
            outputs = {sum((1-((b>>(2*r))&1))<<r for r in range(8)) for a, b in columns}
            constants.append({'depth': depth, 'odd_constant': next(iter(odd)),
                'even_constant': next(iter(even)) if len(even) == 1 else None,
                'recoded_eight_words': sorted(outputs), 'language_preserved': outputs <= ALLOWED})
        else:
            witness = next(i for i, (a, b) in enumerate(columns) if (b>>1)&1 == 0)
            failures.append({'depth': depth, 'gate_word_hex': hex(ordered[witness]), 'odd_bit': 0})
        for pair in columns:
            a, b = pair; pair[:] = [b, ((b>>1)^(b|a))&mask]
    report = {'finite_symbolic_search_only': True, 'Lean_verified': False, 'CQ01Empty_proved': False,
        'gate_bits': h, 'input_eight_words': sorted(ALLOWED), 'word_counts': counts,
        'maximum_depth_tested': 2*h-17, 'constant_odd_columns': constants,
        'nonconstant_column_witnesses': failures}
    path = Path(__file__).with_name(f'gate-language-renormalization-bits{h}.json')
    path.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ['nonconstant_column_witnesses', 'word_counts']}))


if __name__ == '__main__': main()
