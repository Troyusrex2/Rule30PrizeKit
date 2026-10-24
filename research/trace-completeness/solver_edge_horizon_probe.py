"""Bounded SMT falsification; UNSAT and timeout never become Lean premises.

Requires z3-solver and the existing scalar controls. No global settings change.
"""
import argparse
import json
from pathlib import Path
import time
import z3
from control_probes import scalar_trace
from inverse_trace_gap_probe import trace

HERE = Path(__file__).resolve().parent


def model(n, c, h, milliseconds):
    assert n > 1 and 0 <= c < n and h > 0
    width = max(n, c+h)
    a, b = z3.BitVecs('initial_a initial_b', n)
    solver = z3.SolverFor('QF_BV')
    solver.set(timeout=milliseconds, max_memory=1536)
    solver.add(z3.Extract(n-1, n-1, a) == 1,
               z3.Extract(n-1, n-1, b) == 0, b != 0)
    left, right = z3.ZeroExt(width-n, a), z3.ZeroExt(width-n, b)
    for t in range(h):
        solver.add(z3.Extract(c+t, c+t, left) == z3.Extract(c+t, c+t, right))
        left ^= (left << 1) | (left << 2)
        right ^= (right << 1) | (right << 2)
    return solver, a, b


def controls():
    # Independent physical truth-table evolution, followed by every pair in
    # the exact small SMT domain: a in [64,127], b in [1,63], c=1.
    observations = [scalar_trace(a, 1, 14) for a in range(128)]
    longest = -1
    pairs = 0
    for a in range(64, 128):
        for b in range(1, 64):
            delta = observations[a] ^ observations[b]
            assert delta
            longest = max(longest, (delta & -delta).bit_length()-1)
            pairs += 1
    assert longest == 13
    for h, expected in [(13, z3.sat), (14, z3.unsat)]:
        solver, a, b = model(7, 1, h, 2000)
        assert solver.check() == expected
        if expected == z3.sat:
            assignment = solver.model()
            av, bv = assignment.eval(a).as_long(), assignment.eval(b).as_long()
            assert scalar_trace(av, 1, h) == scalar_trace(bv, 1, h)
    return {'all_passed': True, 'independent_scalar_rows': 128,
            'naive_domain_pairs': pairs, 'longest_common_prefix': longest,
            'solver_control_horizons': [13, 14]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--width', type=int, default=32)
    parser.add_argument('--center', type=int, default=8)
    parser.add_argument('--timeout-ms', type=int, default=45000)
    parser.add_argument('--output', type=Path, default=HERE/'solver-edge-horizon-probe.json')
    args = parser.parse_args()
    if not (2 <= args.width <= 64 and 0 <= args.center < args.width):
        parser.error('require width between 2 and 64 and center below width')
    if not 1 <= args.timeout_ms <= 60000:
        parser.error('timeout-ms must be between 1 and 60000')
    checked = controls()
    print(json.dumps({'controls': checked}), flush=True)
    start = time.monotonic()
    n, c = args.width, args.center
    h = 2*n+2
    solver, a, b = model(n, c, h, args.timeout_ms)
    verdict = solver.check()
    report = {'initial_bit_bound': n, 'center_index': c, 'horizon': h,
              'required_first_row_highest_bit': n-1,
              'required_second_row_highest_bit_below': n-1,
              'solver': z3.get_version_string(), 'timeout_ms': args.timeout_ms,
              'solver_verdict': str(verdict), 'controls': checked,
              'Lean_verified': False, 'edge_observability_proved': False,
              'full_problem_solved': False}
    if verdict == z3.sat:
        assignment = solver.model()
        av, bv = assignment.eval(a).as_long(), assignment.eval(b).as_long()
        assert 0 < av < 1 << n and 0 < bv < 1 << n
        assert av.bit_length() != bv.bit_length()
        assert trace(av, c, h) == trace(bv, c, h)
        assert scalar_trace(av, c, h) == scalar_trace(bv, c, h)
        delta = trace(av, c, 2048) ^ trace(bv, c, 2048)
        report.update({'witness': [av, bv], 'independent_integer_and_scalar_checks': True,
                       'first_difference_through_2048': (delta & -delta).bit_length()-1 if delta else None})
    elif verdict == z3.unknown:
        report['reason_unknown'] = solver.reason_unknown()
    report['seconds'] = round(time.monotonic()-start, 3)
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
