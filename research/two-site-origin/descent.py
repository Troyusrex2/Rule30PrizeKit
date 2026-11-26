"""Search and replay finite western rows for a strict additive descent at phase zero."""
from collections import Counter


def tick(x, east):
    # bit 0 is -1; black cells beyond the last bit are absent.
    return (x >> 1) ^ (x | (x << 1) | east)


def macro(x):
    y = tick(x, 0)
    z = tick(y, 1)
    return tick(z, 1) if y & 1 == 0 and z & 1 == 1 else None


def features(x, k):
    mask = (1 << k) - 1
    counts = Counter((x >> j) & mask for j in range(x.bit_length()))
    return [counts[i] for i in range(1, mask+1)] + [int((x & mask) == i) for i in range(mask+1)]


def delta(x,k):
    y = macro(x)
    assert y is not None
    return tuple(b-a for a,b in zip(features(x,k),features(y,k)))


if __name__ == '__main__':
    for k,x in ((1,15),(2,735),(3,8632)):
        assert macro(x) is not None and not any(delta(x,k))
        print(k,x,macro(x))
