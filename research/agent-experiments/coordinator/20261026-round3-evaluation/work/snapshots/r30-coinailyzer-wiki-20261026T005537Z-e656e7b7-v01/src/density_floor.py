# -*- coding: utf-8 -*-
"""Is there a FLOOR on the density of Theta f, and therefore a ceiling on the ratio?

For an eventually-alternating Golden free stream f the zero density is exactly 1/2, so
5*zeros(f,n) - n -> (3/2)n, while blackCount(Theta f, 2n+1) -> d * 2n where d is the
eventual black density of the reconstructed row.  Hence

    ratio(n)  ->  (3/2) / (2 d)  =  3 / (4 d).

The whole question "is there a uniform C" therefore collapses, for this family, to
"is there a positive floor on d".  This script measures d EXACTLY, by detecting the
eventual period of Theta f and counting black cells in one period, over:

  (1) every legal single-slip stream out to a large index;
  (2) every legal two- and three-slip set inside a window.

LEGALITY: a slip flips the parity of the alternating tail, so a slip is Golden only at
a position of the currently-legal parity.  Consecutive slips therefore sit at ODD gaps.
That is a hard constraint on slip schedules and it is what kills the geometric clock in
`slip_gas.py` -- a doubling schedule has an even gap at every step after the first.

Usage:  python -I density_floor.py [max_L]
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
    S = set(slips)
    f, flips = [], 0
    for s in range(n):
        if s in S:
            flips += 1
        f.append((s + phase + flips) % 2)
    return f


def golden(f):
    s = "".join(str(b) for b in f)
    return "00" not in s and "11111" not in s


def exact_density(slips, depth, maxp=600):
    """Exact eventual black density of Theta f, or None if no period <= maxp."""
    f = slip_stream(slips, depth // 2 + 2)
    if not golden(f[:min(len(f), 4 * (max(slips) + 20) if slips else 60)]):
        return None, None, None
    psi = psi_row(f, depth)
    lo = int(depth * 0.75)
    tail = psi[lo:]
    for p in range(1, maxp + 1):
        if len(tail) >= 4 * p and all(tail[i] == tail[i % p] for i in range(len(tail))):
            return Fraction(sum(tail[:p]), p), p, sum(tail[:p])
    return None, None, None


def main():
    maxL = int(sys.argv[1]) if len(sys.argv) > 1 else 240

    print("(1) every legal SINGLE slip, exact eventual density of Theta f")
    print("    ratio_inf = 3/(4d).  Published C=1 witness sits at 7/4, i.e. d = 3/7.")
    print()
    print("  %-6s %-10s %-22s %-12s" % ("L", "density", "period/black", "ratio_inf"))
    best = None
    rows = []
    for L in range(0, maxL + 1):
        depth = 6 * L + 900
        d, p, blk = exact_density([L], depth)
        if d is None:
            continue
        r = Fraction(3, 4) / d
        rows.append((d, L, p, blk, r))
        if best is None or d < best[0]:
            best = (d, L, p, blk, r)
            print("  %-6d %-10s %-22s %-12s   <-- new floor"
                  % (L, d, "%d / %d" % (p, blk), r))
    print()
    print("  lowest density over %d legal single slips, L <= %d: %s at L = %d"
          % (len(rows), maxL, best[0], best[1]))
    print("  implied asymptotic ratio: %s = %.6f" % (best[4], float(best[4])))
    print()

    dens = sorted({d for d, _, _, _, _ in rows})
    print("  the density takes only %d distinct values in this range: %s"
          % (len(dens), ", ".join(str(x) for x in dens[:12])))
    print()

    print("(2) legal TWO- and THREE-slip sets (odd gaps), positions <= 60")
    best2 = None
    for a in range(0, 61, 2):
        for g1 in range(1, 60, 2):
            b = a + g1
            if b > 60:
                break
            d, p, blk = exact_density([a, b], 6 * b + 900)
            if d is None:
                continue
            if best2 is None or d < best2[0]:
                best2 = (d, (a, b), p, blk)
    print("  best two-slip: density %s at %s (period %s, %s black)"
          % (best2[0], list(best2[1]), best2[2], best2[3]) if best2 else "  none")
    best3 = None
    for a in range(0, 41, 2):
        for g1 in range(1, 40, 2):
            for g2 in range(1, 40, 2):
                c = a + g1 + g2
                if c > 60:
                    break
                d, p, blk = exact_density([a, a + g1, c], 6 * c + 900)
                if d is None:
                    continue
                if best3 is None or d < best3[0]:
                    best3 = (d, (a, a + g1, c), p, blk)
    print("  best three-slip: density %s at %s (period %s, %s black)"
          % (best3[0], list(best3[1]), best3[2], best3[3]) if best3 else "  none")
    print()
    print("  single-slip floor %s ; two-slip %s ; three-slip %s"
          % (best[0], best2[0] if best2 else "-", best3[0] if best3 else "-"))


if __name__ == "__main__":
    main()
