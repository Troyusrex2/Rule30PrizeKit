"""Independent physical-cell controls for the seed-boundary reduction.

These finite checks validate coordinates; they do not prove the open premise.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def phi(a):
    return a ^ ((a << 1) | (a << 2))


def next_scalar(cells):
    result = {}
    for p in range(min(cells)-1, max(cells)+2):
        neighborhood = (cells.get(p-1, 0) << 2) | (cells.get(p, 0) << 1) | cells.get(p+1, 0)
        if (30 >> neighborhood) & 1:
            result[p] = 1
    return result


def main():
    scalar = [{0: 1}]
    packed = [1]
    for _ in range(48):
        scalar.append(next_scalar(scalar[-1]))
        packed.append(phi(packed[-1]))
    cells = 0
    for t in range(49):
        for p in range(-t-3, t+4):
            k = t-p
            read = (packed[t] >> k) & 1 if k >= 0 else 0
            assert read == scalar[t].get(p, 0), (t, p)
            cells += 1
        assert packed[t] & 7 in (1, 7)
    pairs = 0
    for T in range(13):
        for P in range(1, 8):
            a, b, c = packed[T] << P, packed[T+P], T+P
            k = 2*(T+P)
            assert a > 0 and a & 1 == 0 and b & 7 in (1, 7)
            assert (b >> k) & 1 and a >> k == 0
            for u in range(9):
                assert (a >> (c+u)) & 1 == scalar[T+u].get(0, 0)
                assert (b >> (c+u)) & 1 == scalar[T+P+u].get(0, 0)
                a, b = phi(a), phi(b)
                pairs += 1
    report = {'verdict': 'pass', 'finite_semantic_controls_only': True,
              'independent_scalar_cell_checks': cells,
              'seed_rows_with_checked_low_bits': 49,
              'aligned_pair_checks': pairs, 'aligned_center_observations': 2*pairs,
              'separation_premise_proved': False, 'full_problem_solved': False}
    (HERE/'seed-boundary-controls.json').write_text(json.dumps(report, indent=2)+'\n',
                                                 encoding='utf-8', newline='\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
