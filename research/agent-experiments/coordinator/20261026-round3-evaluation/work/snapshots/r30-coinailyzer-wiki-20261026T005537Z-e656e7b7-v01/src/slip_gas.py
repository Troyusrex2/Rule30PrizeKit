# -*- coding: utf-8 -*-
"""Slips as particles: does a GAS of phase slips drive the charge ratio past every C?

Round two (response r30-coinailyzer-wiki-20261025T124335Z-f16dc412-v01) established
that both sides of

    CriticalCharge C B R  :=  forall n,
        5*zeros (free R) n <= n + B + C*blackCount (Psi R) (2*n+1)

are functionals of the single free stream f = free R, because Psi R = Theta (free R);
that f is always Golden (no `00`, no `11111`), so the excess 5*zeros(f,n) - n grows at
rate at most 3/2 and only on eventually-alternating f; and that a SINGLE phase slip --
one parity flip in the alternating stream, legal because it creates `11` and not `00` --
is the transient that buys ratios above 7/4 (0x888 gives 21/10, 0x72270 gives ~2.3288).

This script takes the obvious next step and asks the off-the-wall version of it.  A slip
is a localised defect in the alternating ether of the free stream.  Treat slips as
PARTICLES and ask what a gas of them does:

  (B) two slips a distance g apart -- is there an interaction?  Does the pair's row
      density depend on g, or do the two defects act independently?
  (C) k slips on a GEOMETRIC clock, positions m*2^j.  This is the off-the-wall part:
      the ScaleCharges statement measures at cutoff(m,k) = (m+16)*(2^k - 1) and allows
      slack floor(k/2), so the statement itself has a doubling clock built into it.  An
      adversary who slips once per doubling is slipping on the statement's own clock.
  (D) k slips at UNIFORM spacing d, as the control for (C).
  (E) exhaustive search over every Golden slip set inside a window, for the true optimum.

The quantity reported is the exact integer ratio

    ratio(n) = (5*zeros(f,n) - n) / blackCount(Theta f, 2n+1),

whose supremum over achievable f is the least C that can satisfy the inequality.  A ratio
that grows without bound in k would mean no uniform C exists; a ratio that saturates is a
bound.  Achievability (which f are free R for a finite R) is NOT addressed here -- that is
`achievable_slips.py`, and it is where this line of attack is actually decided.

Usage:  python -I slip_gas.py [n]
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coupled_core import psi_row  # noqa: E402

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass


def slip_stream(slips, n, phase=0):
    """Alternating stream with a parity flip at each index in `slips`."""
    S = set(slips)
    f = []
    flips = 0
    for s in range(n):
        if s in S:
            flips += 1
        f.append((s + phase + flips) % 2)
    return f


def golden(f):
    s = "".join(str(b) for b in f)
    return "00" not in s and "11111" not in s


def measure(f, n):
    """Exact (zeros, black, ratio) at horizon n.  Needs len(f) >= n+1."""
    psi = psi_row(f, 2 * n)
    z = sum(1 for i in range(n) if f[i] == 0)
    b = sum(psi[:2 * n + 1])
    return z, b, Fraction(5 * z - n, b) if b else None


def tail_period(psi, lo, maxp=400):
    tail = psi[lo:]
    for p in range(1, maxp + 1):
        if len(tail) >= 4 * p and all(tail[i] == tail[i % p] for i in range(len(tail))):
            return p, sum(tail[:p])
    return None, None


def report(label, slips, n, phase=0):
    f = slip_stream(slips, n + 2, phase)
    if not golden(f[:200]):
        print("  %-34s NOT GOLDEN" % label)
        return None
    z, b, r = measure(f, n)
    psi = psi_row(f, 2 * n)
    p, blk = tail_period(psi, int(2 * n * 0.8))
    per = ("period %d, %d black -> %s" % (p, blk, Fraction(blk, p))) if p else "none <= 400"
    print("  %-34s zeros %-7d black %-7d ratio %-10.6f  %s"
          % (label, z, b, float(r), per))
    return r


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    print("exact integer arithmetic, horizon n = %d, depths 0..%d" % (n, 2 * n))
    print("ratio(n) = (5*zeros(f,n) - n) / blackCount(Theta f, 2n+1)")
    print()

    print("(A) ONE slip at index L -- the round-two baseline, recomputed exactly")
    best_a = (Fraction(0), None)
    for L in range(0, 33):
        r = report("slip at %d" % L, [L], n)
        if r and r > best_a[0]:
            best_a = (r, L)
    print("  best single slip: %s at L = %s" % (best_a[0], best_a[1]))
    print()

    print("(B) TWO slips, first at the single-slip optimum, second a gap g later")
    L0 = best_a[1]
    best_b = (Fraction(0), None)
    for g in range(1, 25):
        r = report("slips at %d, %d (gap %d)" % (L0, L0 + g, g), [L0, L0 + g], n)
        if r and r > best_b[0]:
            best_b = (r, g)
    print("  best gap: %s at g = %s   (single-slip was %s)"
          % (best_b[0], best_b[1], best_a[0]))
    print()

    print("(C) k slips on a GEOMETRIC clock: positions m*2^j, j = 0..k-1")
    for m in (3, 5, 7, 13):
        for k in (2, 3, 4, 5, 6):
            pos = [m * (2 ** j) for j in range(k)]
            if pos[-1] > n // 2:
                continue
            report("m=%-2d k=%d  %s" % (m, k, pos), pos, n)
    print()

    print("(D) k slips at UNIFORM spacing d -- the control for (C)")
    for d in (3, 5, 7, 11, 21):
        for k in (2, 3, 4, 6, 8):
            pos = [L0 + j * d for j in range(k)]
            if pos[-1] > n // 2:
                continue
            report("d=%-2d k=%d  %s" % (d, k, pos), pos, n)
    print()

    print("(E) exhaustive: every Golden slip set inside positions 0..13")
    W = 14
    best = []
    for bits in range(1 << W):
        pos = [i for i in range(W) if (bits >> i) & 1]
        if not pos:
            continue
        f = slip_stream(pos, n + 2)
        if not golden(f[:120]):
            continue
        z, b, r = measure(f, 400)          # cheap screen
        best.append((r, tuple(pos)))
    best.sort(reverse=True)
    print("  %d Golden slip sets in the window; top 10 re-measured at n = %d" % (len(best), n))
    for r_screen, pos in best[:10]:
        report("%s" % (list(pos),), list(pos), n)
    print()
    print("Interpretation is in REPORT.md.  Nothing here is a theorem: every line is a")
    print("finite measurement of a stream whose achievability is decided elsewhere.")


if __name__ == "__main__":
    main()
