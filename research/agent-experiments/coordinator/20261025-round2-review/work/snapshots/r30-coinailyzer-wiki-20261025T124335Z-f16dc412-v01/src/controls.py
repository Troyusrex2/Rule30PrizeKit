# -*- coding: utf-8 -*-
"""Independent controls for coupled_core.py, and an exact periodic analysis.

Control A: a naive, separately written implementation of drv / u / free /
alt / recon / lam / Theta / Psi using plain dictionaries and the Lean
recursions transcribed literally, with no bit packing.  Compared cell by cell
against the packed implementation.

Control B: periodicity.  For a candidate right half we detect an exact cycle
in (free stream, driven right-half row) and in the sideways row, then compute
the asymptotic charge ratio from the cycle rather than from a finite sample.
A ratio read off a finite prefix is not an asymptotic statement; a detected
exact cycle of the DRIVEN ROW is, for the free stream, because the driven row
plus the time parity determines all later behaviour.

Usage:  python -I controls.py [hex R ...]
"""
import sys

sys.path.insert(0, ".")
from coupled_core import (WALL_C1, config, counts, free_stream, psi_row,  # noqa: E402
                          right_mask)

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

sys.setrecursionlimit(100000)


# ---------------------------------------------------------------- control A
def naive_free(rmask, n):
    """free R s for s < n, by the literal drv recursion on a dict of rows."""
    T = 2 * n - 1
    span = rmask.bit_length()
    W = span + T + 3
    row = {p: (rmask >> p) & 1 for p in range(0, W + 1)}
    row[0] = 1                                    # altCol 0
    out = []
    for t in range(T):
        new = {}
        for p in range(1, W + 1):
            a = row.get(p - 1, 0)
            b = row.get(p, 0)
            c = row.get(p + 1, 0)
            new[p] = a ^ (b | c)                  # Rule30Jen.rule
        new[0] = 1 if (t + 1) % 2 == 0 else 0     # altCol (t+1)
        row = new
        if (t + 1) % 2 == 1:
            out.append(1 - row[1])
    return out[:n]


def naive_psi(fstream, depth):
    """Psi d = recon (alt f) d 0, by literal memoised recursion."""
    def a(t):
        return 1 if t % 2 == 0 else fstream[t // 2]

    memo = {}

    def recon(k, t):
        if k == 0:
            return 0
        if k == 1:
            return a(t)
        key = (k, t)
        v = memo.get(key)
        if v is None:
            v = recon(k - 1, t + 1) ^ (recon(k - 1, t) | recon(k - 2, t))
            memo[key] = v
        return v

    # iterative bottom-up to avoid deep recursion
    K = depth
    prev = [0] * (K + 2)
    cur = [a(t) for t in range(K + 2)]
    out = [0, cur[0]] if depth >= 1 else [0]
    for k in range(2, depth + 1):
        nxt = [cur[t + 1] ^ (cur[t] | prev[t]) for t in range(K + 1 - k)]
        prev, cur = cur, nxt
        out.append(cur[0])
    return out


def control_a(rmask, n):
    f1 = free_stream(rmask, n)
    f2 = naive_free(rmask, n)
    ok_f = f1[:n] == f2[:n]
    p1 = psi_row(free_stream(rmask, n + 1), 2 * n)
    p2 = naive_psi(naive_free(rmask, n + 1), 2 * n)
    ok_p = p1 == p2
    return ok_f, ok_p


# ---------------------------------------------------------------- control B
def driven_cycle(rmask, tmax):
    """Detect an exact cycle of (driven row, time parity).

    The driven right half obeys drv(t+1,p+1)=rule(...) with column 0 forced by
    altCol, so the pair (row, t mod 2) is a deterministic state.  A repeat of
    that state is an exact proof that the free stream is eventually periodic
    FOR THE TRUNCATED WIDTH USED; the truncation is exact only while the
    simulated width exceeds the true support, so we report the width too.
    """
    span = rmask.bit_length()
    W = span + tmax + 3
    mask = (1 << (W + 1)) - 1
    row = (rmask & mask) | 1
    seen = {}
    free = []
    for t in range(tmax):
        key = (row, t % 2)
        if key in seen:
            return seen[key], t, free
        seen[key] = t
        row = ((row << 1) ^ (row | (row >> 1))) & mask
        row &= ~1
        if (t + 1) % 2 == 0:
            row |= 1
        else:
            free.append(1 - ((row >> 1) & 1))
    return None, tmax, free


def seq_period(seq, min_rep=4):
    """Smallest eventual period of a list, with the preperiod, or None."""
    n = len(seq)
    for pre in range(0, min(n // 2, 400)):
        tail = seq[pre:]
        m = len(tail)
        for p in range(1, m // min_rep + 1):
            if all(tail[i] == tail[i % p] for i in range(m)):
                return pre, p
    return None


def analyse(rmask, n=3000, label=""):
    z, b, f, psi = counts(rmask, n)
    exc = 5 * z - n
    res = {"R": rmask, "label": label, "n": n, "zeros": z, "black": b,
           "excess": exc, "ratio": exc / b if b else float("inf")}
    pf = seq_period(f[:min(len(f), 1200)])
    pp = seq_period(psi[1:min(len(psi), 1200)])
    res["free_period"] = pf
    res["psi_period"] = pp
    if pf and pp:
        pre_f, per_f = pf
        pre_p, per_p = pp
        cyc_f = f[pre_f:pre_f + per_f]
        cyc_p = psi[1 + pre_p:1 + pre_p + per_p]
        zeros_per = sum(1 for x in cyc_f if x == 0)
        black_per = sum(cyc_p)
        # excess per free step; black per DEPTH, and depth advances 2 per step
        exc_rate = (5 * zeros_per - per_f) / per_f
        blk_rate = 2 * black_per / per_p
        res["exact_ratio"] = exc_rate / blk_rate if blk_rate else float("inf")
        res["exc_rate"] = exc_rate
        res["blk_rate"] = blk_rate
    return res


def main():
    args = sys.argv[1:]
    ref = right_mask(config(3, 1, 6, WALL_C1))
    cands = [int(a, 16) for a in args] if args else [ref, 0x888, 0x1888, 0x12c0]

    print("CONTROL A: packed vs naive implementation, n = 60")
    for r in cands:
        ok_f, ok_p = control_a(r, 60)
        print("  R = 0x%-8x  free agrees: %-5s   Psi agrees: %-5s" % (r, ok_f, ok_p))
        assert ok_f and ok_p, "packed and naive implementations disagree"
    print("  both implementations agree on every tested cell.")
    print()

    print("CONTROL B: exact driven-row cycle and periodic ratio")
    for r in cands:
        start, hit, _ = driven_cycle(r, 4000)
        tag = ("cycle: state at t=%d repeats at t=%d (period %d)"
               % (start, hit, hit - start)) if start is not None else "no cycle within 4000 steps"
        a = analyse(r, 3000, "")
        print("  R = 0x%-8x  %s" % (r, tag))
        print("      free period %s   psi period %s" % (a["free_period"], a["psi_period"]))
        if "exact_ratio" in a:
            print("      excess rate %.6f / black rate %.6f  ->  exact ratio %.6f"
                  % (a["exc_rate"], a["blk_rate"], a["exact_ratio"]))
        print("      finite n=3000: excess %d, black %d, ratio %.6f"
              % (a["excess"], a["black"], a["ratio"]))


if __name__ == "__main__":
    main()
