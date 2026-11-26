"""Standalone independent verifier. Python 3, standard library only.

Grow four-tick column words toward the east. Bit zero is the earliest time.
Keep an edge exactly when both its vertices are in the same strongly connected
component. The first column of a tuple is westernmost.
"""
from collections import Counter


def consistent(west, middle, east):
    for t in range(3):
        a, b, c = ((x >> t) & 1 for x in (west, middle, east))
        if ((middle >> (t + 1)) & 1) != (a ^ (b | c)):
            return False
    return True


def recurrent_extensions(windows):
    edges = {}
    forward, backward = {}, {}
    for win in windows:
        source, dest = tuple(x & 7 for x in win), tuple(x >> 1 for x in win)
        edges[win] = (source, dest)
        forward.setdefault(source, []).append(dest)
        backward.setdefault(dest, []).append(source)
    # Kosaraju, explicit stack. Retain every intra-component edge, including loops.
    seen, order = set(), []
    for root in forward:
        stack = [(root, False)]
        while stack:
            v, closing = stack.pop()
            if closing:
                order.append(v)
            elif v not in seen:
                seen.add(v)
                stack.append((v, True))
                stack.extend((z, False) for z in forward.get(v, ()))
    ids = {}
    for root in reversed(order):
        if root in ids:
            continue
        stack = [root]
        while stack:
            v = stack.pop()
            if v not in ids:
                ids[v] = root
                stack.extend(backward.get(v, ()))
    return {win for win, (u, v) in edges.items() if ids[u] == ids[v]}


def recurrence_at_width(width=19):
    words = range(1, 15)
    # Both endpoints' exterior words may be arbitrary (including both constants).
    right_ok = {(b, c) for b in words for c in words
                if any(consistent(b, c, outside) for outside in range(16))}
    left_ok = {(a, b) for a in words for b in words
               if any(consistent(outside, a, b) for outside in range(16))}
    extend = {(a, b): [c for c in words
                        if consistent(a, b, c) and (b, c) in right_ok]
              for a in words for b in words}
    windows = recurrent_extensions(left_ok & right_ok)
    for w in range(3, width + 1):
        windows = recurrent_extensions(
            (*prefix, c) for prefix in windows for c in extend[prefix[-2:]])
    return windows


def projected_function(windows, k):
    f = {}
    for win in windows:
        source = tuple(x & 7 for x in win[:k])
        dest = tuple(x >> 1 for x in win[:k])
        assert f.setdefault(source, dest) == dest, "projection branches"
    assert set(f) == set(f.values()), "projection is not a permutation"
    return f


def cycle_lengths(f):
    lengths = []
    unseen = set(f)
    while unseen:
        start = next(iter(unseen))
        x, steps = start, 0
        while x in unseen:
            unseen.remove(x)
            x, steps = f[x], steps + 1
        assert x == start
        lengths.append(steps)
    return sorted(lengths)


if __name__ == "__main__":
    wins = recurrence_at_width()
    assert len(wins) == 495
    f = projected_function(wins, 12)
    assert len(f) == 217
    print("19-column recurrent windows:", len(wins))
    print("Western 12-column states:", len(f))
    print("Cycle lengths:", sorted(Counter(cycle_lengths(f)).items()))
