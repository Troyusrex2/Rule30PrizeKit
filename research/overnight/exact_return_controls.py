"""Independent finite tests of the exact eight-column return criterion."""
import json
from pathlib import Path

from right_prefix_safety import double_step


def local_return(word):
    # Scalar temporal reconstruction, not Lean's pair recurrence.
    columns = [[0]*12, [int(t % 2 or not ((word >> (t//2)) & 1)) for t in range(12)]]
    for _ in range(9):
        old, new = columns[-2:]
        columns.append([new[t+1] ^ (new[t] | old[t]) for t in range(len(new)-1)])
    ninth, tenth = columns[9], columns[10]
    d0 = ((word >> 2) ^ (word >> 4)) & 1
    d1 = ((word >> 3) ^ (word >> 5)) & 1
    return ninth[:2] == [1-d0, 1] and tenth[:2] == [d0, d1]


def exact_return_finite(word, width):
    return all(local_return((word >> r) & 63) for r in range(width+1))


def near_spaced_finite(word, width):
    return all(not ((word >> r) & (word >> (r+1)) & 1) for r in range(width+1)) and all(
        not ((word >> (r+1)) & (word >> (r+3)) & 1) for r in range(width+1))


def spaced_finite(word, width):
    return all(not ((word >> r) & (word >> (r+d)) & 1)
               for r in range(width+1) for d in [1, 2])


def main():
    allowed = [w for w in range(64) if local_return(w)]
    width = 12
    comparisons = 0
    transformed = 0
    for word in range(1 << width):
        assert exact_return_finite(word, width) == near_spaced_finite(word, width)
        comparisons += 1
        if spaced_finite(word, width):
            d = (word >> 2) ^ (word >> 4)
            assert exact_return_finite(d, width) == (word >> 5 == 0)
            transformed += 1
    a = 1
    gate = 0
    n = 1024
    for t in range(146+n+16):
        if t >= 146:
            gate |= (a & 1) << (t-146)
        a = double_step(a)
    old_bad = [r for r in range(n) if not local_return((gate >> r) & 63)]
    d = (gate >> 2) ^ (gate >> 4)
    new_bad = [r for r in range(n) if not local_return((d >> r) & 63)]
    assert not old_bad and new_bad
    report = {'finite_controls_only': True, 'unbounded_proof_replaced': False,
        'allowed_six_bit_words': allowed, 'all_zero_tail_words_width': width,
        'exact_return_vs_near_spacing_cases': comparisons,
        'spaced_transform_cases': transformed, 'all_finite_controls_passed': True,
        'actual_empty_gate_start_cycle': 146, 'actual_gate_cycles_tested': n,
        'first_gate_bad_windows': old_bad,
        'transformed_gate_first_bad_window': new_bad[0],
        'transformed_gate_bad_window_count': len(new_bad),
        'prize_problem_proved': False}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
