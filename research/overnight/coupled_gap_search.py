"""Falsify bounded-gap proposals using necessary coupled free-bit constraints.

SAT witnesses are checked by independent forward Rule 30 evolution. UNSAT is
exploratory solver evidence, never kernel evidence or a complete CQ01 claim.
Only no-00/no-11111 is imposed, not realizability by a finite driven right half.
"""
import argparse
import json
from pathlib import Path
import time

import z3


def cone(depth, timeout, spacing35=False):
    solver = z3.Solver()
    solver.set(timeout=timeout)
    old = z3.BitVecVal(0, depth + 1)
    previous = z3.BitVecVal(0, depth + 1)
    cells, free = [], []
    for k in range(depth):
        b = z3.BoolVal(True) if k % 2 == 0 else z3.Bool('f_' + str(k // 2))
        if k % 2:
            free.append(b)
            if len(free) >= 2:
                solver.add(z3.Or(free[-1], free[-2]))
            if len(free) >= 5:
                solver.add(z3.Not(z3.And(*free[-5:])))
            if spacing35 and len(free) >= 3:
                solver.add(z3.Or(free[-3], z3.Not(free[-2]), free[-1]))
            if spacing35 and len(free) >= 5:
                solver.add(z3.Or(free[-5], z3.Not(free[-4]), z3.Not(free[-3]),
                                 z3.Not(free[-2]), free[-1]))
        scan = old | (previous << 1)
        shift = 1
        while shift < k:
            value = z3.BitVec(f'scan_{k}_{shift}', depth + 1)
            solver.add(value == scan ^ (scan << shift))
            scan = value
            shift *= 2
        nxt = z3.BitVec('row_' + str(k + 1), depth + 1)
        mask = (1 << k) - 1
        solver.add(nxt == (((scan ^ z3.If(b, z3.BitVecVal(mask, depth + 1),
                                              z3.BitVecVal(0, depth + 1))) & mask) << 1)
                   | z3.If(b, z3.BitVecVal(1, depth + 1), z3.BitVecVal(0, depth + 1)))
        cells.append(z3.Extract(k, k, nxt) == 1)
        previous, old = old, nxt
    return solver, cells, free


def search(start, gap, timeout, spacing35=False):
    depth = start + gap - 1
    began = time.monotonic()
    solver, cells, free = cone(depth, timeout, spacing35)
    solver.add(*[z3.Not(cells[k - 1]) for k in range(start, start + gap)])
    status = solver.check()
    result = {'start_depth': start, 'white_gap': gap, 'depth': depth,
              'status': str(status), 'seconds': round(time.monotonic() - began, 3)}
    if status == z3.sat:
        model = solver.model()
        bits = [int(z3.is_true(model.eval(c, model_completion=True))) for c in cells]
        f = [int(z3.is_true(model.eval(c, model_completion=True))) for c in free]
        row = sum(b << k for k, b in enumerate(bits))
        assert all(b == 0 for b in bits[start - 1:start + gap - 1])
        assert all(f[j] or f[j + 1] for j in range(len(f) - 1))
        assert all(not all(f[j:j + 5]) for j in range(len(f) - 4))
        # Tail is white for this independent finite check; observations before
        # depth only read the certified prefix. Infinite realizability is open.
        for t in range(depth):
            assert row & 1 == (1 if t % 2 == 0 else f[t // 2])
            row = (row >> 1) ^ (row | (row << 1))
        result.update(initial_prefix=''.join(map(str, bits)),
                      free_prefix=''.join(map(str, f)), independently_checked=True)
    elif status == z3.unknown:
        result['reason'] = solver.reason_unknown()
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cases', nargs='+', default=['8:8', '16:8', '24:8', '32:8',
                                                  '48:8', '64:8', '32:16', '64:16'])
    ap.add_argument('--timeout-ms', type=int, default=15000)
    ap.add_argument('--spacing35', action='store_true')
    args = ap.parse_args()
    path = Path(__file__).parent / ('spacing35-gap-search.json' if args.spacing35
                                   else 'coupled-gap-search.json')
    report = {'finite_experiments_only': True, 'z3_version': z3.get_version_string(),
              'coupled_right_realizability_claim': False,
              'zero_spacings_three_or_five': args.spacing35, 'results': []}
    for case in args.cases:
        result = search(*map(int, case.split(':')), args.timeout_ms, args.spacing35)
        report['results'].append(result)
        path.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
        print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
