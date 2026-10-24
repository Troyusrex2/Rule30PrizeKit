"""Independent physical truth-table checks of the external attaining pairs.

Finite controls only; unrestricted-tail soundness comes from the Lean proof.
"""
import json
from pathlib import Path
import random

HERE = Path(__file__).resolve().parent


def cells_from_lane(left, width, lane):
    code = 2*lane+1
    return {left+i: 1 for i in range(width) if (code >> i) & 1}


def center_trace(cells, count):
    result = []
    for _ in range(count):
        result.append(cells.get(0, 0))
        updated = {}
        for p in range(min(cells)-1, max(cells)+2):
            neighborhood = (cells.get(p-1, 0) << 2) | (cells.get(p, 0) << 1) | cells.get(p+1, 0)
            if (30 >> neighborhood) & 1:
                updated[p] = 1
        cells = updated
    return result


def main():
    rng = random.Random(3099171)
    reports = []
    tail_checks = 0
    for m, d, e, i, j in [(8, 6, 7, 44, 68), (13, 9, 10, 91, 293), (14, 11, 12, 8, 33)]:
        a, b = d-m, e-m
        x = cells_from_lane(a, 2*m+1-d, i)
        y = cells_from_lane(b, 2*m+1-e, j)
        assert min(x) == a and min(y) == b
        tx, ty = center_trace(x, m+1), center_trace(y, m+1)
        assert tx[:m] == ty[:m] and tx[m] != ty[m]
        for original, expected in [(x, tx), (y, ty)]:
            for _ in range(8):
                extended = dict(original)
                extended.update({p: 1 for p in range(m+1, m+21) if rng.randrange(2)})
                assert center_trace(extended, m+1) == expected
                tail_checks += 1
        reports.append({'left_edges': [a, b], 'first_difference_time': m,
                        'lane_indices': [i, j], 'all_checks_passed': True})
    report = {'verdict': 'pass', 'finite_semantic_controls_only': True,
              'external_submission': 'R30-20261024-991a71',
              'attaining_pairs': reports, 'finite_right_tail_extensions_checked': tail_checks,
              'unrestricted_tail_proof_supplied_by_controls': False, 'full_problem_solved': False}
    (HERE/'edge-pairs-991a71-controls.json').write_text(json.dumps(report, indent=2)+'\n',
                                                   encoding='utf-8', newline='\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
