# -*- coding: utf-8 -*-
"""Which slip schedules are actually REALISED by a finite right half?

`density_floor.py` works over IDEAL free streams: alternating with chosen parity slips.
Only streams of the form f = free R for some finite right half R are admissible in the
critical-charge statement, so a low-density ideal stream is worth nothing until a right
half producing it is exhibited.  This script closes (or fails to close) that gap.

For every right half supported in positions 1..W it computes free R, classifies the
stream as alternating-with-k-slips, and records which slip index sets occur.  It then
reports the best ratio actually achieved and, crucially, which of the low-density
schedules of `density_floor.py` were NOT reached.

Usage:  python -I achievable_slips.py [W] [n]
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coupled_core import free_stream, psi_row  # noqa: E402

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass


def slips_of(f):
    """Indices s >= 1 with f[s] == f[s-1]; the stream is alternating between them."""
    return tuple(s for s in range(1, len(f)) if f[s] == f[s - 1])


def ratio_at(f, n):
    psi = psi_row(f, 2 * n)
    z = sum(1 for i in range(n) if f[i] == 0)
    b = sum(psi[:2 * n + 1])
    return Fraction(5 * z - n, b) if b else None


def main():
    W = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 70

    seen = {}                      # slip tuple -> smallest R realising it
    for bits in range(1, 1 << W):
        r = bits << 1              # positions 1..W, position 0 is the wall column
        f = free_stream(r, n)
        s = slips_of(f[:n])
        if s not in seen:
            seen[s] = r

    singles = sorted(s[0] for s in seen if len(s) == 1)
    print("right halves searched: 2^%d - 1 = %d, free stream read to %d terms"
          % (W, (1 << W) - 1, n))
    print("distinct slip schedules realised: %d" % len(seen))
    print("schedules with exactly ONE slip, by index: %s" % (singles,))
    print("highest single-slip index realised: %s"
          % (max(singles) if singles else None))
    print()

    print("exact ratio at n = %d for each realised single-slip stream:" % n)
    best = None
    for L in singles:
        r = seen[(L,)]
        f = free_stream(r, n + 2)
        q = ratio_at(f, n)
        print("  slip at %-4d  R = 0x%-10x  ratio %.6f" % (L, r, float(q)))
        if best is None or q > best[0]:
            best = (q, L, r)
    if best:
        print("  best realised: ratio %.6f at slip index %d, R = 0x%x"
              % (float(best[0]), best[1], best[2]))
    print()

    TARGETS = [(94, "3/14", "7/2"), (190, "1/4", "3"), (26, "2/7", "21/8"),
               (14, "9/28", "7/3"), (2, "5/14", "21/10")]
    print("the low-density single-slip schedules, and whether this search reached them:")
    for L, d, rinf in TARGETS:
        print("  slip at %-4d density %-6s ratio_inf %-6s  %s"
              % (L, d, rinf, "REALISED" if L in singles else "NOT realised in this search"))
    print()
    print("A schedule marked NOT realised is not thereby unachievable: this search covers")
    print("only right halves supported in positions 1..%d.  The missing lemma is stated in" % W)
    print("REPORT.md and it is the whole of the gap between 7/2 and what is exhibited here.")


if __name__ == "__main__":
    main()
