"""Is "centre is P-periodic from time 0" already UNSAT at a finite width?

Rule 30 is permutive in its left argument, so the WHOLE left half-plane is a
deterministic function of two adjacent columns: col0 and col1. Fix those and
every column to their left is forced, with no freedom at all.

Now add what the single-cell seed demands of those forced columns:
    cell(t, -m) = 0   for every t < m      (outside the light cone)
    cell(m, -m) = 1                        (the left edge is black)
Reading N bits of col0 and col1 lets you force columns down to depth ~N, so N
bits of freedom buy you of order N^2/2 constraints. Freedom grows linearly,
obligation quadratically. The real orbit satisfies all of it -- the
constraints are massively dependent -- but the question is whether pinning
col0 to a period collapses the solution set to nothing at a FINITE width.

If the count ever reaches 0 for some (P, N), period P is dead from time 0.
That is not Problem 1, which allows a transient. But for period 2 the kit has
already reduced the prize question to the no-transient form
(Rule30PeriodTwoSideways.CQ01_iff_no_finite_alternating), so there the two
coincide.

Exhaustive DFS over col1 with pruning. No heuristics, no sampling.
"""
import json
import sys

sys.setrecursionlimit(10000)


def survivors(P, pattern, N, want_examples=0):
    """Count col1 prefixes of length N consistent with col0 = `pattern`
    repeated, under the light-cone and black-edge constraints derivable
    from N bits. Returns (count, examples)."""
    col0 = [pattern[t % P] for t in range(N)]
    found = []

    def check(col1, L):
        """All constraints fully determined by col0[:N] and col1[:L].
        Returns False as soon as one fails."""
        # grid[d][t] = cell(t, -d); depth d costs one time step per level
        prev2 = col1[:L]                      # column +1
        prev1 = col0[:]                       # column 0
        for d in range(1, N):
            # cell(t,-d) = cell(t+1,-d+1) XOR (cell(t,-d+1) OR cell(t,-d+2))
            width = min(len(prev1) - 1, len(prev2))
            if width <= 0:
                break
            cur = [prev1[t + 1] ^ (prev1[t] | prev2[t]) for t in range(width)]
            for t in range(width):
                if t < d and cur[t] != 0:
                    return False              # inside the light-cone void
                if t == d and cur[t] != 1:
                    return False              # the left edge must be black
            prev2, prev1 = prev1, cur
        return True

    def dfs(col1):
        L = len(col1)
        if not check(col1, L):
            return 0
        if L == N:
            if want_examples and len(found) < want_examples:
                found.append("".join(map(str, col1)))
            return 1
        return dfs(col1 + [0]) + dfs(col1 + [1])

    return dfs([]), found


out = {}
print("survivor counts: col0 = a fixed P-periodic word, col1 free over N bits")
print("(0 would mean that period is impossible from time 0 at that width)\n")
for P in (1, 2, 3, 4):
    print(f"--- period {P}")
    for pat in range(1 << P):
        pattern = [(pat >> i) & 1 for i in range(P)]
        row = []
        for N in range(4, 19):
            c, _ = survivors(P, pattern, N)
            row.append(c)
            if c == 0:
                break
        tag = "".join(map(str, pattern))
        out[f"P{P}_{tag}"] = row
        verdict = "DEAD at N=%d" % (4 + len(row) - 1) if row[-1] == 0 else "alive"
        print(f"  col0={tag:<4} N=4..{4+len(row)-1}: {row}   {verdict}")
    print()

json.dump(out, open("../evidence/sideways_sat_count.json", "w"), indent=1)
print("wrote ../evidence/sideways_sat_count.json")
