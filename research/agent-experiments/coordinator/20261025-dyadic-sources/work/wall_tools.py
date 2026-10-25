"""Exact finite GF(2) diagnostics; these computations are not Lean proofs."""
from itertools import permutations


def center(rule, count):
    # Bit i at time t is physical cell i-t. Support is exactly contained in [0,2t].
    a = 1
    ans = []
    for t in range(count):
        ans.append((a >> t) & 1)
        if rule == 30:
            a = (a << 2) ^ ((a << 1) | a)
        elif rule == 90:
            a = (a << 2) ^ a
        elif rule == 150:
            a = (a << 2) ^ (a << 1) ^ a
        elif rule == 210:
            # Truth table 11010010: l XOR (r AND NOT c).
            a = (a << 2) ^ (a & ~(a << 1))
        else:
            raise ValueError(rule)
    return ans


def physical_center(rule, count):
    row = {0: 1}
    ans = []
    for t in range(count):
        ans.append(row.get(0, 0))
        row = {x: (rule >> (4*row.get(x-1,0)+2*row.get(x,0)+row.get(x+1,0))) & 1
               for x in range(-t-1, t+2)}
    return ans


def bm(bits):
    c, b, degree, last = 1, 1, 0, -1
    history = 0
    profile = []
    for n, bit in enumerate(bits):
        history = (history << 1) | bit
        if (history & c).bit_count() & 1:
            old = c
            c ^= b << (n-last)
            if 2*degree <= n:
                degree = n+1-degree
                b, last = old, n
        profile.append(degree)
    return profile, c


def det(bits, n, t=0):
    if n == 0:
        return 1
    rows = [sum(bits[t+i+j] << j for j in range(n)) for i in range(n)]
    for j in range(n):
        pivot = next((i for i in range(j,n) if (rows[i] >> j) & 1), None)
        if pivot is None:
            return 0
        rows[j], rows[pivot] = rows[pivot], rows[j]
        for i in range(j+1,n):
            if (rows[i] >> j) & 1:
                rows[i] ^= rows[j]
    return 1


def det_leibniz(bits, n, t=0):
    return sum(all(bits[t+i+j] for i,j in enumerate(p))
               for p in permutations(range(n))) & 1


def leading(bits):
    profile, _ = bm(bits)
    return [1] + [int(profile[2*n-1] == n) for n in range(1,len(bits)//2+1)]


def wall(bits, maxn, maxt):
    assert len(bits) >= 2*maxn+maxt
    ans = [[1]*maxt for _ in range(maxn+1)]
    for t in range(maxt):
        column = leading(bits[t:t+2*maxn])
        for n,d in enumerate(column):
            ans[n][t] = d
    return ans
