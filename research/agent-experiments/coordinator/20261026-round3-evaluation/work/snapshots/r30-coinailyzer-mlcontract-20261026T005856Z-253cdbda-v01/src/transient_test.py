"""The decisive test. Problem 1 allows an arbitrary TRANSIENT: the centre need
only be P-periodic from some time T onward. The width-N refutation of the
no-transient case is worthless if the surviving width grows without bound in T.

col0[t] is free for t < T, then equals pattern[(t-T) % P]. Everything else is
as before: col1 free, the whole left half-plane forced, light-cone void and
black left edge imposed wherever N bits determine them.
"""
import json
import sys
sys.setrecursionlimit(10000)


def widest_survival(P, T, Ncap=20):
    """Widest N at which SOME (transient, pattern, col1) triple survives."""
    best, witness = 0, None
    for pat in range(1 << P):
        pattern = [(pat >> i) & 1 for i in range(P)]
        for tr in range(1 << T):
            transient = [(tr >> i) & 1 for i in range(T)]
            col0_full = transient + [pattern[i % P] for i in range(Ncap + 4)]

            def check(col1, N):
                prev2, prev1 = col1[:], col0_full[:N]
                for d in range(1, N):
                    width = min(len(prev1) - 1, len(prev2))
                    if width <= 0:
                        break
                    cur = [prev1[t + 1] ^ (prev1[t] | prev2[t]) for t in range(width)]
                    for t in range(width):
                        if t < d and cur[t] != 0:
                            return False
                        if t == d and cur[t] != 1:
                            return False
                    prev2, prev1 = prev1, cur
                return True

            def dfs(col1, N):
                if not check(col1, N):
                    return False
                if len(col1) == N:
                    return True
                return dfs(col1 + [0], N) or dfs(col1 + [1], N)

            lo = 4
            while lo <= Ncap and dfs([], lo):
                if lo > best:
                    best, witness = lo, ("".join(map(str, transient)),
                                         "".join(map(str, pattern)))
                lo += 1
    return best, witness


print("widest surviving width N, as the allowed transient T grows")
print("(if this climbs without limit the method cannot reach Problem 1)\n")
print("   T |  P=1   P=2   P=3   P=4")
out = {}
for T in range(0, 9):
    row = []
    for P in (1, 2, 3, 4):
        b, w = widest_survival(P, T)
        row.append(b)
        out[f"T{T}_P{P}"] = {"widest_N": b, "witness": w}
    print(f"  {T:2d} | " + "  ".join(f"{v:4d}" for v in row))
json.dump(out, open("../evidence/transient_test.json", "w"), indent=1)
print("\nwrote ../evidence/transient_test.json")
