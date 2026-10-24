"""Exact finite-clock discovery for an eventually smaller-clock right tail.

The graph has a fixed temporal clock, hence this is not an arbitrary-clock
proof. No SAT or graph answer is labelled Lean verified. Every tail vertex
has an infinite right continuation at the smaller clock.
"""
import argparse
from collections import deque
import json
from pathlib import Path
import time


def integrate(source, p):
    value = source
    shift = 1
    while shift < p:
        value ^= value << shift
        shift *= 2
    return (value << 1) & ((1 << p)-1)


def lower_live(half):
    if half not in (1, 2, 4, 8):
        raise ValueError('Exhaustive lower graph is guarded to half clocks 1,2,4,8')
    size = 1 << half
    mask = size-1
    # Edge (a,b) -> (b,c) runs towards the spatial right.
    predecessors = [[] for _ in range(size*size)]
    degree = [0]*(size*size)
    for b in range(size):
        for c in range(size):
            source = b | c
            if source.bit_count() % 2:
                continue
            a = integrate(source, half)
            target = b | (c << half)
            for first in (a, a ^ mask):
                pred = first | (b << half)
                degree[pred] += 1
                predecessors[target].append(pred)
    dead = deque(i for i, d in enumerate(degree) if d == 0)
    while dead:
        v = dead.popleft()
        for u in predecessors[v]:
            degree[u] -= 1
            if degree[u] == 0:
                dead.append(u)
    return [i for i, d in enumerate(degree) if d > 0]


def probe(half, state_limit=2000000, seconds=50):
    started = time.monotonic()
    p = 2*half
    mask = (1 << p)-1
    lower_mask = (1 << half)-1
    live = lower_live(half)
    queue = deque()
    seen = {}
    for key in live:
        b, c = key & lower_mask, key >> half
        lifted = (b | (b << half)) | ((c | (c << half)) << p)
        seen[lifted] = None
        queue.append(lifted)
    edges = 0
    loss = None
    stopped = None
    while queue:
        key = queue.popleft()
        b, c = key & mask, key >> p
        source = b | c
        if source.bit_count() % 2:
            continue
        a = integrate(source, p)
        for first in (a, a ^ mask):
            edges += 1
            target = first | (b << p)
            smaller_first = (first & lower_mask) == (first >> half)
            smaller_second = (b & lower_mask) == (b >> half)
            if smaller_first and not smaller_second:
                path = [target, key]
                while seen[path[-1]] is not None:
                    path.append(seen[path[-1]])
                loss = {'profile_pairs_to_lower_tail': [str(k) for k in path]}
                queue.clear()
                break
            if target not in seen:
                seen[target] = key
                queue.append(target)
        if len(seen) >= state_limit:
            stopped = 'state guard'
            break
        if time.monotonic()-started >= seconds:
            stopped = 'time guard'
            break
    return {'Lean_verified': False, 'full_problem_claim': False,
            'half_clock': half, 'full_clock': p,
            'lower_clock_right_live_pairs': len(live),
            'reachable_full_clock_pairs': len(seen), 'edges': edges,
            'queue_remaining': len(queue), 'stopped_reason': stopped,
            'complete_at_fixed_clock': stopped is None and loss is None,
            'period_loss': loss, 'seconds': round(time.monotonic()-started, 3)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--half-clock', type=int, default=8)
    ap.add_argument('--seconds', type=int, default=50)
    args = ap.parse_args()
    result = probe(args.half_clock, seconds=args.seconds)
    Path(__file__).with_name('clock-onset-graph-'+str(args.half_clock)+'.json').write_text(
        json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
