"""Literal one-update audit of root's specified width-four candidate.

No BFS, SAT, temporal sweep, or all-time claim is made.
"""
from pathlib import Path
import hashlib
import json

SOURCE = Path('D:/MWB/Rule30/agent-inbox/r30-codex-cedar-followup-20261026T154236Z-b768c9a6-v02/clock-review/published/work/dependencies/Rule30CommonPastResearch.lean')
SOURCE_SHA = '17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3'


def unpack(x, n=4):
    return tuple((x >> j) & 1 for j in range(n))


def pack(xs):
    return sum(b << j for j, b in enumerate(xs))


def actual_lookup(xs):
    q = (0, 0) + tuple(xs)
    return tuple((30 >> (4 * q[j + 2] + 2 * q[j + 1] + q[j])) & 1
                 for j in range(len(xs)))


def actual_xor_or(xs):
    return tuple(x ^ ((xs[j - 1] if j else 0) | (xs[j - 2] if j >= 2 else 0))
                 for j, x in enumerate(xs))


def mode_source_cases(a, b, h):
    out = [h[0], h[1] ^ h[0]]
    for j in range(2, len(h)):
        out.append(h[j] ^ ((1 - b[j - 2]) & h[j - 1])
                   ^ ((1 - a[j - 1]) & h[j - 2]))
    return tuple(out)


def mode_white_padding(a, b, h):
    aa, bb, hh = (0, 0) + a, (0, 0) + b, (0, 0) + h
    return tuple(int(bool(hh[j + 2]) !=
                     ((not bool(bb[j]) and bool(hh[j + 1])) !=
                      (not bool(aa[j + 1]) and bool(hh[j]))))
                 for j in range(len(h)))


def properties(a, b, h):
    d = tuple(x ^ y for x, y in zip(a, b))
    common = [(d[j] & h[j + 1]) == (h[j] & d[j + 1]) for j in range(len(h) - 1)]
    subset = [(h[j] & d[j]) == h[j] for j in range(len(h))]
    return {'A': pack(a), 'B': pack(b), 'H': pack(h), 'D': pack(d),
            'A_older_first': ''.join(map(str, a)),
            'B_older_first': ''.join(map(str, b)),
            'H_older_first': ''.join(map(str, h)),
            'D_older_first': ''.join(map(str, d)),
            'common_adjacent_checks': common, 'common': all(common),
            'subset_coordinate_checks': subset, 'subset': all(subset)}


def main():
    own = Path(__file__).resolve().parent
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA
    for marker in ('STOP', 'STOP_RESEARCH'):
        if (own.parents[1] / marker).exists():
            raise SystemExit('Session stop flag: ' + marker)
    a, b, h = unpack(1), unpack(2), unpack(8)
    aa, bb = actual_lookup(a), actual_lookup(b)
    hh = mode_source_cases(a, b, h)
    assert aa == actual_xor_or(a) and bb == actual_xor_or(b)
    assert hh == mode_white_padding(a, b, h)
    assert (pack(aa), pack(bb), pack(hh)) == (7, 14, 8)
    before, after = properties(a, b, h), properties(aa, bb, hh)
    assert before['common'] and after['common'] and after['subset']
    assert not before['subset'] and before['subset_coordinate_checks'] == [True, True, True, False]
    result = {
        'status': 'Exact proposed finite-word backward-one-step Subset implication refuted',
        'width': 4, 'integer_convention': 'bit j is cell j; least significant bit is oldest',
        'boundary': 'genuine missing older white A=B=H=0; no right-edge wrap',
        'source': str(SOURCE), 'source_sha256': SOURCE_SHA,
        'formula': "H'_j=H_j xor((not B_(j-2)) and H_(j-1)) xor((not A_(j-1)) and H_(j-2)); white padding gives H'_0=H_0 and H'_1=H_1 xor H_0",
        'input': before, 'output': after,
        'refuted_statement': 'For every finite white-ended triple row, Common(input) and Common(output) and Subset(output) imply Subset(input).',
        'controls': ['literal Rule30 truth table equals triangular XOR/OR for A and B',
                     'piecewise frozen Mode definition equals independent Boolean white-padding implementation',
                     'all three actual adjacent pairs satisfy Common in both rows',
                     'all four output positions satisfy Subset; input fails exactly at j3'],
        'search_performed': False, 'BFS_performed': False, 'temporal_steps_checked': 1,
        'all_time_Common_asserted': False,
        'scope_limit': 'This is a finite-prefix two-row counterexample only. No all-time Common history or infinite-half-line completion is supplied; no implication about full Common/Mode initial-Subset preservation or safety completeness follows.',
        'next_action': 'Stop this candidate route; no extra horizons, BFS, or SAT.',
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (own / 'audit.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
