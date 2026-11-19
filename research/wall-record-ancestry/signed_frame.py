"""Exact signed arithmetic for the all-white-past test (paper companion)."""

def P(n):
    return n ^ ((n << 1) | (n << 2))


def inverse(y):
    if y < 0:
        raise ValueError("the image of P consists of nonnegative integers")
    prev = prior = value = 0
    bits = y.bit_length()+2
    for i in range(bits):
        bit = ((y >> i) & 1) ^ (prev | prior)
        value |= bit << i
        prior, prev = prev, bit
    assert prior == prev
    return value - (prev << bits)


def F(n):
    return (n >> 1) ^ (n | (n << 1))


def white_depth(y):
    if y <= 0:
        raise ValueError("positive initial row required")
    k = 0
    while y > 0:
        old = inverse(y)
        if old < 0:
            return k
        # This is the predecessor in physical coordinates.
        y = 2 * old
        k += 1
    raise AssertionError("a nonzero orbit cannot reach zero here")


if __name__ == "__main__":
    for n in range(-2048, 2049):
        assert P(n)>=0 and inverse(P(n))==n
    for y in range(4096):
        assert P(inverse(y))==y
        u,v=y%2,F(y)%2
        assert P(y>>1) == F(y) ^ (u + 2*u*v)
    # Direct k-white inversion equals membership in the unsigned k-fold
    # image of P until the first negative intermediate value.
    for y in range(1,2049):
        k = 0
        cur = y
        while (cur := inverse(cur)) >= 0:
            k += 1
        assert white_depth(y) == k
    print("Signed round trips, low-bit forcing, and physical ancestry depth passed.")
