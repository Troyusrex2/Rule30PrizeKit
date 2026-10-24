"""Independent physical-coordinate Rule 30 controls for the ancestry witness."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def initial(a, c):
    return {c-k: (a >> k) & 1 for k in range(a.bit_length())}


def step(row):
    if not row:
        return {}
    return {p: (30 >> ((row.get(p-1, 0) << 2) |
                       (row.get(p, 0) << 1) | row.get(p+1, 0))) & 1
            for p in range(min(row)-1, max(row)+2)}


def main():
    cells = 0
    traces = []
    for a in [49, 42]:
        row = initial(a, 2)
        packed = a
        observed = []
        for t in range(18):
            observed.append(row.get(0, 0))
            for p in range(min(row), max(row)+1):
                k = 2+t-p
                assert k >= 0
                assert row[p] == ((packed >> k) & 1)
                cells += 1
            row = step(row)
            packed ^= (packed << 1) | (packed << 2)
        traces.append(observed)
    first = next(t for t, (a, b) in enumerate(zip(*traces)) if a != b)
    assert first == 17
    parent_checks = 0
    for a in range(64):
        physical = step(initial(a, 0))
        result = sum(bit << (1-p) for p, bit in physical.items())
        assert result == a ^ ((a << 1) | (a << 2))
        if a == 15:
            assert result == 49
        if a < 16:
            assert result != 42
        parent_checks += 1
    report = {'all_passed': True, 'physical_cells_compared': cells,
        'one_step_parent_controls': parent_checks, 'first_difference_time': first,
        'rows': [49, 42], 'center_index': 2, 'Lean_verified_by_this_script': False,
        'unbounded_no_parent_claim_from_controls': False,
        'full_problem_solved': False}
    (HERE/'ancestry-controls.json').write_text(json.dumps(report, indent=2)+'\n',
        encoding='utf-8', newline='\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
