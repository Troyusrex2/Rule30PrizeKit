"""Small independent truth-table replay of the arbitrary-height construction."""
from itertools import product


def rule(deep, middle, shallow):
    return (30 >> (4*deep + 2*middle + shallow)) & 1


def step(x):
    return sum(rule((x >> (j+1)) & 1, (x >> j) & 1, (2*x >> j) & 1) << j
               for j in range(x.bit_length()+1))


def advance(x, k):
    for _ in range(k):
        x = step(x)
    return x


def precursor(y, wall):
    a, b, x = 0, wall, wall
    for j in range(y.bit_length()+2):
        deeper, = [c for c in (0, 1) if rule(c, b, a) == ((y >> j) & 1)]
        a,b = b,deeper
        x |= b << (j+1)
    if a or b:
        assert a == b == 1
        return None
    assert step(x) == y and x & 1 == wall
    return x


def check(H, k, prefix):
    B = H+1+6*k
    stripe = sum(1 << i for i in range(0,B,2))
    outer = advance(stripe | (1 << (B+1)), k)
    mask = (1 << H)-1
    assert outer.bit_length() == H+7*k+3
    y = (outer & ~mask) | prefix
    rows = {y}
    for _ in range(k):
        rows = {precursor(r, b) for r in rows for b in (0, 1)}
        assert None not in rows
    assert len(rows) == 1 << k
    assert all(precursor(r,b) is None for r in rows for b in (0,1))
    if k:
        z = y ^ (1 << (y.bit_length()-2))
        assert all(precursor(z,b) is None for b in (0,1))
        for t in range(H):
            assert (y ^ z) & 1 == 0
            y,z = step(y),step(z)


if __name__ == '__main__':
    count = 0
    for H in range(5):
        for k in range(6):
            for prefix in range(1 << H):
                check(H,k,prefix)
                count += 1
    print(count, "complete finite trees checked, including all children of the last level.")
