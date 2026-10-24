"""Physical truth-table controls for controlled right-half state growth."""
import json
from pathlib import Path
import random

HERE = Path(__file__).resolve().parent


def terminal_normalize(bits):
    while len(bits) >= 3:
        if bits[-3:] == [0, 1, 1]:
            bits = bits[:-3]+[0, 1]
        elif bits[-3:] == [1, 0, 1]:
            bits = bits[:-3]+[1, 1]
        else:
            break
    return bits


def main():
    rng = random.Random(301100)
    drivers = [[0], [1], [0, 1], [0, 0, 1], [1, 1, 0, 0, 1]]
    cases = cells = 0
    constant_head = 0
    for n in [0, 1, 3, 7, 16, 32]:
        for cap in [4, 7]:
            a = (cap << n) | rng.getrandbits(n)
            for driver in drivers:
                row = {k+1: (a >> k) & 1 for k in range(n+3)}
                packed = a
                for t in range(65):
                    bits = [row[p] for p in range(1, max(row)+1)]
                    assert len(bits) == n+t+3
                    assert terminal_normalize(bits) == bits
                    assert packed.bit_length() == n+t+3
                    for k, bit in enumerate(bits):
                        assert bit == ((packed >> k) & 1)
                        cells += 1
                    if n == 0 and cap == 7 and driver == [0]:
                        assert row[1] == 1
                        constant_head += 1
                    b = driver[t % len(driver)]
                    old = {0: b, **row}
                    row = {p: (30 >> ((old.get(p-1, 0) << 2) |
                                      (old.get(p, 0) << 1) | old.get(p+1, 0))) & 1
                           for p in range(1, max(row)+2)}
                    head = b ^ int(bool(packed & 3))
                    packed = 2*(packed ^ ((packed >> 1) | (packed >> 2)))+head
                cases += 1
    report = {'all_passed': True, 'cases': cases, 'physical_cells_compared': cells,
        'time_range': [0, 64], 'constant_head_observations': constant_head,
        'drivers': drivers, 'Lean_verified_by_this_script': False,
        'unbounded_conclusions_from_controls': False, 'full_problem_solved': False}
    (HERE/'controls.json').write_text(json.dumps(report, indent=2)+'\n',
        encoding='utf-8', newline='\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
