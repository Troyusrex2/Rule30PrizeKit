"""F002 ingredient: do iterates of Rule 30 have nontrivial additive conserved
densities (conservation laws) of window length m?

Bulk orientation is the kit's ZBL orientation without the wall:
  new[j] = old[j+1] XOR (old[j] OR old[j-1])   (j increasing = depth increasing)
which is Rule 30 mirrored in index; conservation-law structure is identical.

phi : {0,1}^m -> Q, normalised phi(0^m) = 0. Phi(z) = sum of phi over all
length-m windows of a finite configuration z on a white background.
phi is a conserved density of G = Rule30^k iff phi o G - phi is a coboundary,
iff (fundamental cycles of the de Bruijn graph through 0^(n-1), n = m + 2k)
    Phi(G(e)) = Phi(e)   for every word e of length n.
Trivial solutions (coboundaries psi(w[1:]) - psi(w[:-1]), psi(0^(m-1)) = 0)
span a space of dimension 2^(m-1) - 1, so the equation matrix has rank
<= 2^(m-1) always.  We certify rank >= 2^(m-1) by exhibiting that rank over
GF(p) on a SUBSET of the equations (rank over GF(p) of an integer submatrix
is a lower bound for its rank over Q, which is a lower bound for the full
matrix).  Equality then proves: every rational conserved density of window
length m for Rule30^k is trivial (constant + coboundary).  This is exact,
not sampling-dependent in its conclusion: a failure to reach the target
would only be inconclusive, and is reported as such.
"""
import sys, json, time
import numpy as np

P = 2147483647

RULE = 30

def evolve(words, n, k):
    """words: uint64 array of n-bit words (bit i = cell i). Returns bit matrix
    of the bi-infinite image after k steps, cells -k..n-1+k (length n+2k)."""
    N = len(words)
    width = n + 2 * k + 2  # one extra zero on each side as guard
    cells = np.zeros((N, width), dtype=np.uint8)
    for i in range(n):
        cells[:, k + 1 + i] = (words >> np.uint64(i)) & np.uint64(1)
    for _ in range(k):
        new = np.zeros_like(cells)
        l = cells[:, 2:].astype(np.int64); c = cells[:, 1:-1].astype(np.int64); r = cells[:, :-2].astype(np.int64)
        new[:, 1:-1] = ((RULE >> (4 * l + 2 * c + r)) & 1).astype(np.uint8)  # l = deeper cell old[j+1]
        cells = new
    return cells[:, 1:-1]

def window_counts(cells, m):
    """cells: (N, w) bits; count vector over windows of length m of 0^(m-1) cells 0^(m-1)."""
    N, w = cells.shape
    pad = np.zeros((N, w + 2 * (m - 1)), dtype=np.int64)
    pad[:, m - 1:m - 1 + w] = cells
    C = np.zeros((N, 1 << m), dtype=np.int64)
    rows = np.arange(N)
    for s in range(w + m - 1):
        code = np.zeros(N, dtype=np.int64)
        for t in range(m):
            code |= pad[:, s + t] << t
        np.add.at(C, (rows, code), 1)
    return C[:, 1:]  # drop window 0^m (phi normalised to 0 there)

def rank_mod_p(A, target):
    A = (A % P).astype(np.int64)
    r = 0; R, Cn = A.shape
    for c in range(Cn):
        if r == R or r >= target: break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0: continue
        piv = r + nz[0]
        if piv != r: A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy(); col[r] = 0
        idx = np.nonzero(col)[0]
        if len(idx):
            A[idx] = (A[idx] - (col[idx, None] * A[r][None, :]) % P) % P
        r += 1
    return r

def run(m, k, samples, seed=1):
    n = m + 2 * k
    rng = np.random.default_rng(seed)
    if (1 << n) <= samples:
        words = np.arange(1 << n, dtype=np.uint64)
    else:
        small = np.arange(1 << min(n, 12), dtype=np.uint64)
        rand = rng.integers(0, 1 << n, size=samples, dtype=np.uint64)
        words = np.unique(np.concatenate([small, rand]))
    before = np.zeros((len(words), n + 2 * k), dtype=np.uint8)
    for i in range(n):
        before[:, k + i] = (words >> np.uint64(i)) & np.uint64(1)
    after = evolve(words, n, k)
    A = window_counts(after, m) - window_counts(before, m)
    target = 1 << (m - 1)
    t = time.time()
    r = rank_mod_p(A, target)
    return {"rule": RULE, "m": m, "k_steps": k, "equations_used": int(len(words)), "unknowns": (1 << m) - 1,
            "trivial_rank_upper_bound": target, "rank_mod_p_lower_bound": r,
            "certified_only_trivial_conserved_densities": r == target, "seconds": round(time.time() - t, 2)}

if __name__ == "__main__":
    RULE = int(sys.argv[4]) if len(sys.argv) > 4 else 30
    out = []
    for k in [int(x) for x in sys.argv[1].split(',')]:
        for m in range(int(sys.argv[5]) if len(sys.argv) > 5 else 1, int(sys.argv[2]) + 1):
            res = run(m, k, samples=max(4 * (1 << m), 4096))
            print(json.dumps(res), flush=True); out.append(res)
    json.dump({"rule": RULE, "orientation": "new[j]=f(old[j+1],old[j],old[j-1]), f=(rule>>(4l+2c+r))&1", "prime": P, "results": out}, open(sys.argv[3], "w"), indent=1)
