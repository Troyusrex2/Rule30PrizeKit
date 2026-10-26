# -*- coding: utf-8 -*-
"""Independent check of the L = 94 headline, on a second implementation.

`controls.py` carries a separately written, non-bit-packed transcription of the Lean
recursions (dicts and literal `recon`, no machine words).  The L = 94 density is the
only new numerical claim this response rests on, so it is recomputed here through that
second path and compared cell for cell.

Usage:  python -I verify_94.py
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coupled_core import psi_row            # noqa: E402
from controls import naive_psi              # noqa: E402
from density_floor import slip_stream, golden  # noqa: E402

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

L = 94
DEPTH = 1600
NS = (1000, 2000, 4000, 8000, 14000)


def main():
    f = slip_stream([L], 2 * max(NS) + 4)
    print("free stream: alternating with one slip at index %d, Golden = %s"
          % (L, golden(f[:400])))
    print("  f[88:100] = %s" % "".join(str(b) for b in f[88:100]))

    fast = psi_row(f, DEPTH)
    slow = naive_psi(f, DEPTH)
    assert len(fast) == len(slow), (len(fast), len(slow))
    diff = [k for k in range(len(fast)) if fast[k] != slow[k]]
    print("  bit-packed vs literal recursion over depths 0..%d: %d disagreements"
          % (DEPTH, len(diff)))
    assert not diff

    lo = int(DEPTH * 0.75)
    tail = fast[lo:]
    per = None
    for p in range(1, 600):
        if len(tail) >= 4 * p and all(tail[i] == tail[i % p] for i in range(len(tail))):
            per = (p, sum(tail[:p]))
            break
    print("  eventual period %s, black per period %s, density %s"
          % (per[0], per[1], Fraction(per[1], per[0])))
    d = Fraction(per[1], per[0])
    print("  asymptotic ratio 3/(4d) = %s = %.6f" % (Fraction(3, 4) / d, float(Fraction(3, 4) / d)))

    print()
    print("finite-n check of the same stream, exact integers:")
    print("  %-8s %-10s %-10s %-12s %-16s" % ("n", "zeros", "black", "ratio", "5z-n-3*black"))
    for n in (1000, 2000, 4000, 8000, 14000):
        psi = psi_row(f, 2 * n)
        z = sum(1 for i in range(n) if f[i] == 0)
        b = sum(psi[:2 * n + 1])
        print("  %-8d %-10d %-10d %-12.6f %-16d" % (n, z, b, (5 * z - n) / b, 5 * z - n - 3 * b))
    print()
    print("5*zeros - n - 3*blackCount is NEGATIVE through the transient -- it is still")
    print("-336 at n = 2000 -- crosses zero between n = 2000 and n = 4000, and then grows")
    print("(93, 954, 2235).  Unbounded growth is what refuting C = 3 requires, and this is")
    print("the shape of it; the crossing point is late because the pre-slip prefix of the")
    print("row is dense.  All of it is CONDITIONAL on the stream being free R for some")
    print("finite R, which is not known.  See F003 in REPORT.md.")


if __name__ == "__main__":
    main()
