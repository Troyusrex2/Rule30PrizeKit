"""Falsify a frozen rank using independent long-alternation finite starts.

For the empty initial right half and prescribed alternating center, compute
the required left-neighbor trace, then invert its finite cone with the actual
alternating driver. Cut off the left row after N cells. Forward simulation
checks every claimed alternating observation before testing the rank.
No infinite alternating finite start is asserted or produced.
"""

import argparse
import json
from pathlib import Path
from time import perf_counter

import paired_nonlocal_rank_probe as pair
import restart_nonlocal_rank_probe as restart
from three_inverse_cone_probe import inverse


def alternating_start(length, right_initial=0):
    right = right_initial
    boundary = head = 0
    for t in range(length):
        center = int(t % 2 == 0)
        next_center = 1-center
        boundary |= center << t
        left = next_center ^ (center | (right & 1))
        head |= left << t
        # Actual Rule 30 on the finite right half, with center as its driver.
        right = ((right << 1) | center) ^ (right | (right >> 1))
    left = inverse(head, boundary, length)
    reflected = sum(((left >> k) & 1) << (length-k-1) for k in range(length))
    row = reflected | (1 << length) | (right_initial << (length+1))
    low = (row & -row).bit_length()-1
    return row >> low, length-low


def validate(model_path, lengths, steps, output, right_starts=(0,)):
    from restart_regional_sdp import score

    began = perf_counter()
    model = json.loads(model_path.read_text(encoding='utf-8'))['result']
    report = {'Lean_verified': False, 'full_problem_solved': False,
              'rank_proved': False, 'independent_structured_family': True,
              'candidate_accepted': False, 'cases': []}
    for length, right_initial in ((n, r) for n in lengths for r in right_starts):
        row, center = alternating_start(length, right_initial)
        initial = row
        initial_center = center
        history = []
        for t in range(length+1):
            assert (row >> center) & 1 == int(t % 2 == 0)
            history.append((row, center))
            row, center = pair.step(row), center+1
        tested = failed = 0
        worst = None
        for t in range(1, min(length-2, steps+1)):
            row, center = history[t]
            record = restart.transition(row, center, 2)
            assert record is not None and record[5] == 1
            old, new = score(record, model, False), score(record, model, True)
            residual = new-old+1
            tested += 1
            if residual > 1e-5:
                failed += 1
                if worst is None or residual > worst['residual']:
                    worst = {'construction_depth': length, 'right_initial': str(right_initial), 'evolved_steps': t,
                             'row': str(row), 'center': center, 'lag': 2,
                             'residual': residual, 'old_score': old, 'new_score': new}
        case = {'construction_depth': length, 'right_initial': str(right_initial), 'initial_row': str(initial),
                'initial_center_index': initial_center, 'alternating_observations_checked': length+1,
                'tested_restart_pairs': tested, 'descent_failures': failed, 'worst': worst}
        report['cases'].append(case)
        report['seconds'] = perf_counter()-began
        output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({k: v for k, v in case.items() if k != 'initial_row'}), flush=True)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--model', type=Path, required=True)
    parser.add_argument('--lengths', type=int, nargs='+', default=[16, 32, 64, 128, 256])
    parser.add_argument('--steps', type=int, default=32)
    parser.add_argument('--right-starts', type=int, nargs='+', default=[0])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    validate(args.model, args.lengths, args.steps, args.output, args.right_starts)
