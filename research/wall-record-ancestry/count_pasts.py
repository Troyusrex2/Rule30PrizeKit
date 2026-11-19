"""Check the finite-width counting identity for individual earlier words."""
from collections import Counter


def step(x):
    return (x >> 1) ^ (x | (x << 1))


def observe(x, n):
    word = 0
    for t in range(n):
        word |= (x & 1) << t
        x = step(x)
    return word, x


def check(W, H, k):
    outputs = Counter(observe(y,H)[0] for y in range(1<<(W-1),1<<W))
    eligible = {}
    for x in range(1<<(W-k-1),1<<(W-k)):
        b,y = observe(x,k)
        assert y.bit_length()==W
        u = observe(y,H)[0]
        bucket=eligible.setdefault((b,u),set())
        assert y not in bucket
        bucket.add(y)
    for b in range(1<<k):
        for u in range(1<<H):
            count = len(eligible[b,u])
            assert count == 1 << (W-H-2*k-1)
            assert outputs[u] == count * 4**k


def edge_check(W, H, k):
    # In this regime the complete observed prefix already reaches the
    # top of the only possible ancestor. Compare decoder and forward census.
    census = Counter()
    for x in range(1<<(W-k-1),1<<(W-k)):
        b,y = observe(x,k)
        u,_ = observe(y,H)
        census[b | (u<<k)] += 1
    n = H+k
    for w in range(1<<n):
        x = 0
        for j in range(n):
            _,at_j = observe(x,j)
            x |= (((w>>j)^at_j)&1)<<j
        assert census[w] == int(x.bit_length()==W-k)


if __name__ == "__main__":
    tests = 0
    for W in range(1,13):
        for H in range(5):
            for k in range(5):
                if W >= H+2*k+1:
                    check(W,H,k)
                    tests += 1
    print(tests,"width/window/depth triples; every past and future word checked.")
    edge_cases = 0
    for H in range(5):
        for k in range(5):
            for W in range(k+1,H+2*k+1):
                edge_check(W,H,k)
                edge_cases += 1
    print(edge_cases,"triples in the seed-edge regime; exact zero-or-one counts passed.")
