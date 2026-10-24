"""Exact finite discovery and independent controls for the infinite profile example.

The proof for all times and depths is in Rule30PeriodicProfileCounterResearch.
The finite graph below allows arbitrary infinite right continuations, unlike
temporal_profile_probe.py's zero-boundary reachable component.
"""
from collections import deque
import json
from pathlib import Path


def graph(clock):
    mask = (1 << clock)-1
    n = 1 << (2*clock)
    edges, predecessors = [[] for _ in range(n)], [[] for _ in range(n)]
    for source in range(n):
        b, c = source & mask, source >> clock
        rhs = b | c
        if rhs.bit_count() % 2: continue
        a = bit = 0
        for t in range(clock):
            a |= bit << t
            bit ^= (rhs >> t) & 1
        for new in [a, a ^ mask]:
            target = new | (b << clock)
            edges[source].append(target)
            predecessors[target].append(source)
    indegree = list(map(len, predecessors))
    live = bytearray([1])*n
    queue = deque(j for j, count in enumerate(indegree) if not count)
    while queue:
        source = queue.popleft()
        live[source] = 0
        for target in edges[source]:
            indegree[target] -= 1
            if not indegree[target]: queue.append(target)
    seen, counter = {}, None
    for key in range(n):
        if not live[key]: continue
        a, b = key & mask, key >> clock
        observation = a | b
        if observation in [0, mask]: continue
        if observation in seen and (seen[observation] & mask) != a:
            counter = [seen[observation], key]
            break
        seen[observation] = key
    def extract(key):
        seen, path = {}, []
        while key not in seen:
            seen[key] = len(path)
            path.append(key)
            key = min(p for p in predecessors[key] if live[p])
        profiles = [p & mask for p in path]
        cut = seen[key]
        return {'prefix_profiles': profiles[:cut], 'periodic_tail_profiles': profiles[cut:]}

    def period(profile):
        n = clock
        while n > 1 and all((profile >> t) & 1 == (profile >> (t % (n//2))) & 1
                            for t in range(clock)):
            n //= 2
        return n

    loss = None
    for key in range(n):
        if not live[key]: continue
        a, b = key & mask, key >> clock
        if period(a) < period(b):
            loss = {'head_period': period(a), 'neighbor_period': period(b), 'example': extract(key)}
            break
    paths = [extract(key) for key in counter or []]
    return {'clock': clock, 'all_profile_pairs': n, 'pairs_with_infinite_right_continuations': sum(live),
            'nonconstant_OR_head_ambiguity_found': counter is not None, 'examples': paths,
            'head_period_loss': loss}


def scalar_controls(example, horizon=128, window=32):
    prefix, tail = example['prefix_profiles'], example['periodic_tail_profiles']

    def profile(k):
        return prefix[k] if k < len(prefix) else tail[(k-len(prefix)) % len(tail)]

    width = 2*horizon+window+2
    row = sum((profile(k) & 1) << k for k in range(width))
    heads, ors = [], []
    for t in range(horizon):
        heads.append(row & 1)
        ors.append((row | (row >> 1)) & 1)
        for k in range(window): assert (row >> k) & 1 == (profile(k) >> (t % 8)) & 1
        # Independent whole-integer update, not the profile integration graph.
        row ^= (row >> 1) | (row >> 2)
    return heads, ors


def main():
    cases = [graph(clock) for clock in [2, 4, 8]]
    examples = cases[-1]['examples']
    assert examples == [
        {'prefix_profiles': [45, 43, 186, 166], 'periodic_tail_profiles': [101, 149, 86, 89]},
        {'prefix_profiles': [42, 45, 51, 170], 'periodic_tail_profiles': [170, 85]}]
    a, b = map(scalar_controls, examples)
    assert a[0] != b[0] and a[1] == b[1] and 0 in a[1] and 1 in a[1]
    loss = cases[-1]['head_period_loss']
    assert loss == {'head_period': 2, 'neighbor_period': 8, 'example': {
        'prefix_profiles': [85, 87, 168, 212], 'periodic_tail_profiles': [172, 178, 202, 43]}}
    c = scalar_controls(loss['example'])
    assert c[0] == [1-t%2 for t in range(128)]
    neighbor = [(87 >> t) & 1 for t in range(8)]
    assert all(any(neighbor[(t+p) % 8] != neighbor[t] for t in range(8)) for p in range(1, 8))
    report = {'finite_discovery_and_controls_only': True, 'full_problem_claim': False,
        'finite_support_conjecture_refuted': False, 'cases': cases,
        'independent_integer_horizon': 128, 'independent_integer_window': 32,
        'independent_scalar_cells_checked': 3*128*32, 'checks_passed': True,
        'first_eight_head_profiles': [a[0][:8], b[0][:8]], 'first_eight_shared_OR_profile': a[1][:8]}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n',
        encoding='utf-8', newline='\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'cases'}))


if __name__ == '__main__':
    main()
