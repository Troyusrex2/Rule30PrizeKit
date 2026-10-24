"""Exact inverse cones for the open C3w(011) finite-left problem.

No solver answer is a Lean proof. A finite witness is forward checked with
independent cellwise Rule 30. Unknown/timeouts are never called unsatisfiable.
The trace phases are (*,0,1), with prescribed boundary (0,1,0).
"""

import argparse
import json
from pathlib import Path
import random
from time import perf_counter

import z3


def inverse(head, boundary, length):
    """Recover initial spatial bits from a temporal trace of `length` bits."""
    row = 0
    previous, current = boundary, head
    for k in range(length):
        row |= (current & 1) << k
        previous, current = current, ((current >> 1) ^ (current | previous)) & ((1 << (length-k-1))-1)
    return row


def forward_scalar(row, length):
    cells = [(row >> i) & 1 for i in range(row.bit_length())]+[0]*(length+2)
    trace = 0
    for t in range(length):
        trace |= cells[0] << t
        boundary = int(t % 3 == 1)
        cells = [cells[i+1] ^ (cells[i] | (boundary if i == 0 else cells[i-1]))
                 for i in range(len(cells)-1)]
    return trace


def forward_packed(row, length):
    trace = 0
    for t in range(length):
        trace |= (row & 1) << t
        row = (row >> 1) ^ (row | (row << 1) | int(t % 3 == 1))
    return trace


def controls():
    rng = random.Random(202610240842)
    for n in range(1, 97):
        head = rng.getrandbits(n)
        boundary = sum(int(t % 3 == 1) << t for t in range(n))
        row = inverse(head, boundary, n)
        assert forward_scalar(row, n) == head == forward_packed(row, n)
    return 96


def search(width, cycles, timeout_ms):
    started = perf_counter()
    length = 3*cycles
    assert 0 < width < length
    head = z3.BitVec('head', length)
    fixed_mask = sum(1 << t for t in range(length) if t % 3)
    fixed_bits = sum(1 << t for t in range(length) if t % 3 == 2)
    solver = z3.SolverFor('QF_BV')
    solver.set(timeout=timeout_ms)
    solver.add(head & fixed_mask == fixed_bits)
    previous = z3.BitVecVal(sum(1 << t for t in range(length) if t % 3 == 1), length)
    current = head
    for k in range(length):
        if k >= width:
            solver.add(z3.Extract(0, 0, current) == 0)
        if k+1 < length:
            nxt = z3.BitVec(f'column_{k+1}', length-k-1)
            solver.add(nxt == z3.Extract(length-k-2, 0,
                z3.LShR(current, 1) ^ (current | previous)))
            previous = z3.Extract(length-k-2, 0, current)
            current = nxt
    status = solver.check()
    out = {'width_bound': width, 'cycles': cycles, 'head_observations': length,
           'status': str(status), 'seconds': perf_counter()-started,
           'Lean_verified': False, 'C3w_proved': False, 'full_problem_solved': False}
    if status == z3.sat:
        proposed = solver.model().eval(head).as_long()
        boundary = sum(1 << t for t in range(length) if t % 3 == 1)
        row = inverse(proposed, boundary, length)
        assert row.bit_length() <= width
        assert forward_scalar(row, length) == proposed == forward_packed(row, length)
        out.update(row=str(row), actual_width=row.bit_length(), head_profile=str(proposed),
                   independent_forward_checks_passed=True)
        # Extend until the first forced-phase violation; never call finite
        # agreement an all-time witness, including when the guard is reached.
        state = row
        violation = None
        for t in range(max(4096, length)):
            if t % 3 and (state & 1) != int(t % 3 == 2):
                violation = t
                break
            state = (state >> 1) ^ (state | (state << 1) | int(t % 3 == 1))
        assert violation is None or violation >= length
        out['first_forced_phase_violation'] = violation
        out['extension_guard'] = max(4096, length)
    elif status == z3.unknown:
        out['reason'] = solver.reason_unknown()
    return out


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases', nargs='+', default=['24:14', '32:18', '40:22'])
    parser.add_argument('--timeout-ms', type=int, default=15000)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = {'Lean_verified': False, 'inverse_scalar_controls': controls(), 'results': []}
    for case in args.cases:
        result = search(*map(int, case.split(':')), args.timeout_ms)
        report['results'].append(result)
        args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
        print(json.dumps(result), flush=True)
