"""Falsify finite-tail OR-trace rigidity before attempting an unbounded proof.

The hypotheses tested here are NOT assumed in Lean. The fixed-clock search
can refute them, but its failure to find a counterexample proves neither.
"""
import argparse
from collections import deque
import json
from pathlib import Path
import random
import time

import psutil

from clock_onset_graph_probe import integrate


def bad_constant_OR(head, obs, mask, alt):
    return obs == mask and head not in (0, mask, alt, alt ^ mask)


def infinite_control():
    table = [85, 87, 168, 212, 172, 178, 202, 43]
    profile = lambda k: table[k if k < 4 else 4+(k-4) % 4]
    row = sum((profile(k) & 1) << k for k in range(82))
    for t in range(32):
        for k in range(16):
            assert (row >> k) & 1 == (profile(k) >> (t % 8)) & 1
        row ^= (row >> 1) | (row >> 2)
    return 32*16


def orbit_profile(word, clock):
    head = neighbor = 0
    original = word
    for t in range(clock):
        head |= (word & 1) << t
        neighbor |= ((word >> 1) & 1) << t
        word ^= (word >> 1) | (word >> 2)
    assert word == original
    return head, head | neighbor


def probe(clock, limit):
    assert clock >= 2 and clock & (clock-1) == 0
    started = time.monotonic()
    mask = (1 << clock)-1
    alt = sum(1 << t for t in range(0, clock, 2))
    rows = {0: 0}
    observations = {0: (0, 0)}
    queue = deque([0])
    aliases = 0
    next_guard = 100000
    counter = None
    reason = None
    while queue:
        key = queue.popleft()
        b, c = key & mask, key >> clock
        source = b | c
        if source.bit_count() % 2:
            continue
        first = integrate(source, clock)
        for a in (first, first ^ mask):
            word = (rows[key] << 1) | (a & 1)
            obs = a | b
            if bad_constant_OR(a, obs, mask, alt):
                assert orbit_profile(word, clock) == (a, obs)
                counter = {'kind': 'constant OR with head not of period two', 'word': str(word),
                           'head': str(a), 'OR': str(obs), 'scalar_check_passed': True}
                break
            if obs in observations and observations[obs][0] != a:
                aliases += 1
                other_head, other_word = observations[obs]
                if obs not in (0, mask):
                    assert orbit_profile(word, clock) == (a, obs)
                    assert orbit_profile(other_word, clock) == (other_head, obs)
                    counter = {'kind': 'same nonconstant OR with different heads',
                               'words': [str(word), str(other_word)], 'head_profiles': [str(a), str(other_head)],
                               'OR': str(obs), 'scalar_check_passed': True}
                    break
            else:
                observations[obs] = (a, word)
            target = a | (b << clock)
            if target not in rows:
                rows[target] = word
                queue.append(target)
        if counter:
            break
        if len(rows) >= limit:
            reason = 'state guard'
            break
        if len(rows) >= next_guard:
            next_guard += 100000
            if (psutil.Process().memory_info().rss > 1400*1024**2
                    or time.monotonic()-started > 60):
                reason = 'memory or time guard'
                break
    samples = random.Random(20261024).sample(list(rows), min(256, len(rows)))
    for key in samples:
        a, b = key & mask, key >> clock
        assert orbit_profile(rows[key], clock) == (a, a | b)
    # The existing verified infinite-tail example really violates the
    # constant-OR candidate. Finiteness must not disappear from a proof.
    assert bad_constant_OR(87, 87 | 168, 255, 85)
    assert not bad_constant_OR(mask, mask, mask, alt)  # the one-cell fixed state
    infinite_cells = infinite_control()
    return {'Lean_verified': False, 'full_problem_claim': False, 'clock': clock,
            'states': len(rows), 'OR_classes': len(observations), 'head_aliases': aliases,
            'queue_remaining': len(queue), 'stopped_reason': reason,
            'complete_at_this_fixed_clock': counter is None and reason is None,
            'counterexample': counter, 'unbounded_rigidity_proved': False,
            'controls': {'finite_scalar_orbit_checks': len(samples),
                         'known_infinite_counter_detected': True,
                         'infinite_counter_scalar_cells': infinite_cells,
                         'one_cell_fixed_state_allowed': True, 'AllPassed': True},
            'seconds': round(time.monotonic()-started, 3)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--clock', type=int, default=128)
    ap.add_argument('--state-limit', type=int, default=1500000)
    args = ap.parse_args()
    report = probe(args.clock, args.state_limit)
    Path(__file__).with_name('finite-or-rigidity-'+str(args.clock)+'.json').write_text(
        json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
