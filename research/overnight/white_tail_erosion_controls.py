"""Finite controls for the separately proved white-tail erosion theorem.

No solver, NumPy or Lean assumptions. A cellwise right-half update checks the
packed implementation on selected examples. Wolfram independently compares
those examples to built-in Rule 30 until the first departure of the prefix.
"""
import json
from pathlib import Path
import random
import time


HERE = Path(__file__).resolve().parent
COLUMNS = ['001', '001', '011', '110', '010', '010',
           '110', '101', '100', '100', '101', '011']


def ether(j, t):
    return int(COLUMNS[j % 12][t % 3])


def step(a, boundary):
    return ((a << 1) | boundary) ^ (a | (a >> 1))


def main():
    started = time.monotonic()
    rng = random.Random(301024)
    cases = []
    scalar_cells = 0
    worst = None
    count = 0
    for j in range(12):
        for phase in range(3):
            for sample in range(40):
                k = rng.randrange(1, 33) if sample else 32 + 4 * j
                W = k + rng.randrange(0, 97)
                word = rng.getrandbits(W)
                word = (word & ~((1 << k) - 1)) | sum(
                    ether(j + p, phase) << (p - 1) for p in range(1, k + 1))
                initial = word
                bound = 3 * (W + 12 - k) + 6
                departure = None
                scalar = None
                if sample == 0 and phase == j % 3:
                    scalar = [ether(j, phase)] + [(word >> p) & 1 for p in range(W)]
                    scalar += [0] * (2 * bound + 16)
                for t in range(bound + 1):
                    assert word >> (W + t) == 0
                    if scalar is not None:
                        assert scalar[0] == ether(j, t + phase)
                        assert all(scalar[p] == ((word >> (p - 1)) & 1)
                                   for p in range(1, len(scalar)))
                        scalar_cells += len(scalar) - 1
                    pattern = sum(ether(j + p, t + phase) << (p - 1)
                                  for p in range(1, k + 1))
                    if word & ((1 << k) - 1) != pattern:
                        departure = t
                        break
                    word = step(word, ether(j, t + phase))
                    if scalar is not None:
                        old = scalar
                        scalar = [ether(j, t + phase + 1)] + [
                            old[p - 1] ^ (old[p] | old[p + 1])
                            for p in range(1, len(old) - 1)] + [0]
                assert departure is not None, (j, phase, k, W, initial)
                count += 1
                record = {'attachment': j, 'phase': phase, 'prefix': k,
                          'support_bound': W, 'initial_right_word': str(initial),
                          'first_departure': departure, 'proposed_bound': bound}
                if worst is None or departure > worst['first_departure']:
                    worst = record
                if scalar is not None:
                    cases.append(record)
    report = {'AllPassed': True, 'finite_controls_only': True,
              'Lean_verified_by_this_calculation': False, 'full_problem_claim': False,
              'packed_cases': count, 'independent_cellwise_cases': len(cases),
              'cellwise_comparisons': scalar_cells, 'worst_delay_case': worst,
              'seconds': round(time.monotonic() - started, 3)}
    (HERE / 'white-tail-erosion-controls.json').write_text(
        json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
    (HERE / 'white-tail-erosion-control-cases.json').write_text(
        json.dumps({'finite_controls_only': True, 'cases': cases}, indent=2) + '\n',
        encoding='utf-8', newline='\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
