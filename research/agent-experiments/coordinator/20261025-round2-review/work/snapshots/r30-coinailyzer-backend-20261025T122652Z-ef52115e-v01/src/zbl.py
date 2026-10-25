"""Exact zero-boundary-left (ZBL) Rule 30 primitives, matching the kit's
Rule30ZeroBoundary.zrow convention: depth 0 is the white wall, a word w has
w[i] = cell at depth i+1, cells beyond the word are white.
new(k) = old(k+1) XOR (old(k) OR old(k-1)) for k >= 1."""

def step(w):
    """One ZBL time step on a finite word; returns a word of length len(w)+1
    (the new last cell may be black). No truncation of the front."""
    n = len(w)
    c = [0] + list(w) + [0, 0]
    out = [c[k+1] ^ (c[k] | c[k-1]) for k in range(1, n+2)]
    return out

def next2(w):
    """Kit's Rule30FiniteLeftWordResearch.next: two updates, length+2."""
    return step(step(w))

def strip(w):
    w = list(w)
    while w and w[-1] == 0:
        w.pop()
    return w

def col1(w, T):
    """depth-1 column for times 0..T-1"""
    out = []
    cur = list(w)
    for t in range(T):
        out.append(cur[0] if cur else 0)
        cur = step(cur)
    return out

ETHER7 = [1,1,0,0,0,0,1]
def ether(n, phase=0):
    return [ETHER7[(i+phase) % 7] for i in range(n)]
