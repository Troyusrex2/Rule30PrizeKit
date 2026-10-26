"""Audit only root's explicit four-cycle and its one-step half-line mismatch."""
from pathlib import Path
import hashlib
import json
from audit_candidate import (SOURCE, SOURCE_SHA, unpack, pack, actual_lookup,
                             actual_xor_or, mode_source_cases, mode_white_padding,
                             properties)


def next_row(a, b, h):
    aa, bb, hh = actual_lookup(a), actual_lookup(b), mode_source_cases(a, b, h)
    assert aa == actual_xor_or(a) and bb == actual_xor_or(b)
    assert hh == mode_white_padding(a, b, h)
    return aa, bb, hh


def main():
    own = Path(__file__).resolve().parent
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA
    for marker in ('STOP', 'STOP_RESEARCH'):
        if (own.parents[1] / marker).exists():
            raise SystemExit('Session stop flag: ' + marker)
    initial = (unpack(1), unpack(2), unpack(8))
    current = initial
    trace = []
    for t in range(4):
        row = properties(*current)
        row['phase'] = t
        trace.append(row)
        current = next_row(*current)
    assert current == initial
    assert [r['A'] for r in trace] == [1, 7, 9, 15]
    assert [r['B'] for r in trace] == [2, 14, 2, 14]
    assert [r['H'] for r in trace] == [8, 8, 8, 8]
    assert all(r['common'] for r in trace)
    assert [r['subset'] for r in trace] == [False, True, True, False]
    # A has four distinct values, so the joint cycle's least period is four.
    assert len({r['A'] for r in trace}) == 4
    # With all three initial half-line rows zero after index3, one update has
    # support contained in0..5. Seven cells also check its last possible
    # nonzero-to-zero adjacency; every remaining adjacency is identically zero.
    padded = (unpack(1, 7), unpack(2, 7), unpack(8, 7))
    padded_next = next_row(*padded)
    global_before = properties(*padded)
    global_after = properties(*padded_next)
    assert (global_after['A'], global_after['B'], global_after['H']) == (7, 14, 56)
    assert [j for j, ok in enumerate(global_after['subset_coordinate_checks']) if not ok] == [4, 5]
    assert [j for j, ok in enumerate(global_after['common_adjacent_checks']) if not ok] == [3]
    result = {
        'status': 'Specified fixed-width4 all-time Common cycle audited; prefix-only Subset preservation refuted',
        'width': 4, 'least_joint_period': 4,
        'integer_convention': 'least significant bit is oldest',
        'boundary': 'missing older A,B,H white; only three internal adjacent pairs; no right-edge wrap',
        'cycle': trace, 'literal_wrap_verified': True,
        'all_time_Common_on_internal_pairs': True,
        'phase1_shift': {'initial': {'A': 7, 'B': 14, 'H': 8},
                         'initial_Subset': True, 'Subset_after1': True,
                         'Subset_after2': False, 'failure_coordinate': 3},
        'zero_padded_half_line_original_phase': {'before': global_before,
                                               'after': global_after,
                                               'output_support_bound': 5,
                                               'Subset_failure_coordinates': [4, 5],
                                               'Common_failure_adjacent_pair': [3, 4]},
        'exact_scope': 'Refutes Subset preservation for fixed finite prefixes with all-time Common only on internal pairs, even with genuine older white boundary and actual finite-prefix recurrence.',
        'not_claimed': ['all-time Common for all natural spatial indices',
                        'a whole-half-line initial-Subset counterexample',
                        'a safety-completeness or prize counterexample'],
        'no_search': True, 'no_BFS': True, 'no_extra_horizon': True,
        'source_sha256': SOURCE_SHA,
        'candidate_source_sha256': hashlib.sha256((own / 'audit_candidate.py').read_bytes()).hexdigest(),
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (own / 'cycle-audit.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: result[k] for k in ('status', 'least_joint_period',
                                          'phase1_shift', 'zero_padded_half_line_original_phase',
                                          'exact_scope')}, indent=2))


if __name__ == '__main__':
    main()
