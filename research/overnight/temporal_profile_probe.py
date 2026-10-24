"""All-width finite-clock falsification of diagonal observability hypotheses.

Temporal columns A,B,C obey delta(A)=B OR C. Starting with the zero right
boundary, exhaustive integration constructs every finite-width Q orbit whose
full temporal period divides the selected power-of-two clock. This remains
an untrusted experiment, not a Lean certificate or a center-column theorem.
"""
import argparse
from collections import deque
from functools import lru_cache
import json
from pathlib import Path
import random
import time

import psutil

from controlled_response_normal_form import normal_form


def q(row):
    return row ^ ((row >> 1) | (row >> 2))


def validate_orbit(row, clock):
    initial = row
    head = neighbor = 0
    for t in range(clock):
        head |= (row & 1) << t
        neighbor |= ((row >> 1) & 1) << t
        row = q(row)
    assert row == initial
    return head, neighbor


def search(clock, limit, seconds, output):
    assert clock > 0 and clock & (clock-1) == 0
    mask = (1 << clock)-1
    began = time.monotonic()

    @lru_cache(maxsize=100000)
    def period(profile):
        p = clock
        while p > 1:
            half = p//2
            if ((profile >> half) | ((profile & ((1 << half)-1)) << (clock-half))) != profile:
                break
            p = half
        return p

    def integrate(source):
        # All prefix XORs, shifted so the initial temporal value is zero.
        value = source
        shift = 1
        while shift < clock:
            value ^= value << shift
            shift *= 2
        return (value << 1) & mask

    rows = {0: 0}
    observations = {0: 0}
    queue = deque([0])
    edges = merges = response_merges = 0
    max_width = 0
    counter = loss = None
    stop = None
    next_report = 100000
    controls = None

    def report():
        return {'untrusted_finite_clock_experiment': True, 'Lean_verified': False,
            'prize_problem_proved': False, 'clock': clock,
            'covers_all_widths_for_this_clock': not queue and stop is None and loss is None and counter is None,
            'states': len(rows), 'queued_states': len(queue), 'edges': edges,
            'profile_pair_merges': merges, 'head_or_response_merges': response_merges,
            'head_or_response_classes': len(observations),
            'maximum_representative_width': max_width, 'stopped_reason': stop,
            'head_period_loss': loss, 'normal_form_counterexample': counter,
            'independent_controls': controls,
            'seconds': round(time.monotonic()-began, 3)}

    while queue:
        key = queue.popleft()
        b, c = key & mask, key >> clock
        source = b | c
        if source.bit_count() % 2:
            continue
        a = integrate(source)
        previous_period = period(b)
        for new_head in [a, a ^ mask]:
            edges += 1
            target = new_head | (b << clock)
            word = (rows[key] << 1) | (new_head & 1)
            max_width = max(max_width, word.bit_length())
            head_period = period(new_head)
            if head_period < previous_period:
                expected = (new_head, b)
                assert validate_orbit(word, clock) == expected
                loss = {'word': str(word), 'previous_word': str(rows[key]),
                    'new_head_period': head_period, 'previous_head_period': previous_period,
                    'independent_orbit_check_passed': True}
                break
            observation = new_head | ((new_head | b) << clock)
            if observation in observations:
                response_merges += 1
                other = observations[observation]
                if normal_form(word) != normal_form(other):
                    first = validate_orbit(word, clock)
                    second = validate_orbit(other, clock)
                    assert first[0] == second[0] and (first[0] | first[1]) == (second[0] | second[1])
                    counter = {'words': [str(word), str(other)],
                        'normal_forms': [str(normal_form(word)), str(normal_form(other))],
                        'same_observation': 'head and OR of first two cells',
                        'individual_second_columns_equal': first[1] == second[1],
                        'independent_orbit_check_passed': True}
                    break
            else:
                observations[observation] = word
            if target in rows:
                merges += 1
                if normal_form(word) != normal_form(rows[target]):
                    assert validate_orbit(word, clock) == validate_orbit(rows[target], clock)
                    counter = {'words': [str(word), str(rows[target])],
                        'normal_forms': [str(normal_form(word)), str(normal_form(rows[target]))],
                        'independent_orbit_check_passed': True}
                    break
            else:
                rows[target] = word
                queue.append(target)
            if len(rows) >= limit:
                stop = 'state guard'
                break
        if loss or counter or stop:
            break
        if len(rows) >= next_report:
            rss = psutil.Process().memory_info().rss
            if rss > 1500*1024**2 or psutil.virtual_memory().available < 2*1024**3:
                stop = 'memory guard'
            elif time.monotonic()-began > seconds:
                stop = 'time guard'
            output.write_text(json.dumps(report(), indent=2)+'\n', encoding='utf-8', newline='\n')
            if len(rows) >= 500000 and next_report % 500000 == 0:
                print(json.dumps({'stage': 'progress', **report()}), flush=True)
            next_report += 100000
            if stop:
                break
    # Independent whole-row scalar evolution checks the profile construction.
    # This runs on successful searches too, rather than only on counterexamples.
    samples = random.Random(20261024).sample(list(rows), min(256, len(rows)))
    for key in samples:
        assert validate_orbit(rows[key], clock) == (key & mask, key >> clock)
    small_periodic = small_represented = 0
    for word in range(1 << 10):
        value = word
        head = neighbor = 0
        for t in range(clock):
            head |= (value & 1) << t
            neighbor |= ((value >> 1) & 1) << t
            value = q(value)
        if value == word:
            small_periodic += 1
            key = head | (neighbor << clock)
            if key in rows:
                small_represented += 1
                assert normal_form(word) == normal_form(rows[key])
            elif not queue and stop is None and counter is None and loss is None:
                raise AssertionError('Complete graph omitted a small periodic row')
    controls = {'sampled_profile_pairs_checked_by_full_scalar_orbit': len(samples),
        'all_small_words_checked': 1 << 10, 'small_word_width': 10,
        'small_full_period_divides_clock': small_periodic,
        'small_periodic_words_represented_in_graph': small_represented,
        'checks_passed': True}
    result = report()
    output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--clock', type=int, default=64)
    ap.add_argument('--state-limit', type=int, default=2000000)
    ap.add_argument('--seconds', type=float, default=90)
    args = ap.parse_args()
    output = Path(__file__).with_name(f'temporal-profile-clock{args.clock}.json')
    print(json.dumps(search(args.clock, args.state_limit, args.seconds, output)), flush=True)


if __name__ == '__main__':
    main()
