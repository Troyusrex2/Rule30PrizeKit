"""Second check, using finite seed rows and forward evolution at every leaf."""
from certificate import build


def step(x):
    return (x >> 1) ^ (x | (x << 1))


def seed(n, word):
    # Flipping cell t first flips the wall at tick t (left permutivity).
    x = 0
    for t in range(n):
        y = x
        for _ in range(t):
            y = step(y)
        if (y ^ (word >> t)) & 1:
            x |= 1 << t
    return x


def check_word(n, word):
    a, b = seed(n, word), seed(n, word ^ 1088)
    x, y = a, b
    for t in range(n):
        assert (x & 1) == (word >> t) & 1
        assert (y & 1) == ((word ^ 1088) >> t) & 1
        if t < 11:
            # The deepest possible changed output at t+1 cannot see
            # beyond the input prefix prescribed by this wall word.
            assert (x ^ y).bit_length() + 1 <= n - t - 1
        if t == 11:
            assert x == y
        x, y = step(x), step(y)
    return a, b


def check_tree(node, gaps=()):
    n = 17 + sum(gaps)
    zeros = [0, 6, 16]
    for g in gaps:
        zeros.append(zeros[-1] + g)
    word = (1 << n) - 1 - sum(1 << t for t in zeros)
    assert (n, word) == (node.length, node.word)
    if node.index is not None:
        check_word(n, word)
        return [(len(gaps), node.index, n)]
    six, ten = node.children
    return check_tree(six, gaps + (6,)) + check_tree(ten, gaps + (10,))


if __name__ == "__main__":
    leaves = check_tree(build())
    assert len(leaves) == 1272
    assert sum(1 << (24-level) for level, _, _ in leaves) == 1 << 24
    print("leaves, maximum gap count, spatial depth, ticks:",
          len(leaves), *map(max, zip(*leaves)))
    g = (6,) * 24
    n = 17 + sum(g)
    w = (1 << n) - 1 - sum(1 << t for t in (0, 6, *range(16, n, 6)))
    print("finite seeds, 24 further six-tick returns:", check_word(n, w))
