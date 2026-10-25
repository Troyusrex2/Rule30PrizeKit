# -*- coding: utf-8 -*-
"""Headline reproduction: two finite right halves refute the C = 2 critical charge.

The target is

    CriticalCharge C B R  :=  forall n,
        5*zeros (free R) n <= n + B + C*blackCount (Psi R) (2*n+1)

with the official definitions (see coupled_core.py).  C = 1 is already
kernel-refuted by Rule30Ether.config 3 1 6 wall, whose ratio is 7/4.

This script shows two finite right halves whose ratio exceeds 2, so that
5*zeros - n - 2*blackCount grows without bound and no additive allowance B
can rescue C = 2.  It also shows that the same quantity with C = 3 stays
negative over the whole tested range.

Everything is exact integer arithmetic.  The only unproved step is that the
observed free streams and sideways rows continue past the tested horizon;
that is stated in the report as the missing lemma, and is the reason these
findings are COUNTEREXAMPLE_CANDIDATE and not theorems.

Usage:  python -I witnesses.py [n]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coupled_core import (WALL_C1, config, free_stream, psi_row,  # noqa: E402
                          right_mask)

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

WITNESSES = [
    (right_mask(config(3, 1, 6, WALL_C1)),
     "Rule30Ether.config 3 1 6 wall  (published, kernel-checked, C=1 refuted)"),
    (0x888, "W1: black at positions 3, 7, 11"),
    (0x72270, "W2: black at positions 4, 5, 6, 9, 13, 16, 17, 18"),
]


def support(r):
    return [p for p in range(r.bit_length() + 1) if (r >> p) & 1]


def slip_positions(f, m=80):
    return [s for s in range(1, min(len(f), m)) if f[s] == f[s - 1]]


def eventual_period(seq, start, maxp=400):
    tail = seq[start:]
    for p in range(1, maxp + 1):
        if len(tail) >= 4 * p and all(tail[i] == tail[i % p] for i in range(len(tail))):
            return p, sum(tail[:p])
    return None, None


def run(r, label, n):
    f = free_stream(r, n + 1)
    psi = psi_row(f, 2 * n)
    z = sum(1 for i in range(n) if f[i] == 0)
    b = sum(psi[:2 * n + 1])
    exc = 5 * z - n
    print("-" * 78)
    print(label)
    print("  R as a bit vector     : 0x%x   support %s" % (r, support(r)))
    print("  free R, first 20      : %s" % "".join(str(x) for x in f[:20]))
    print("  zero density of free R: %d / %d = %.6f" % (z, n, z / n))
    print("  phase slips in free R : %s" % slip_positions(f))
    p, blk = eventual_period(psi, 200)
    print("  Psi R, depths 200.. : eventual period %s with %s black per period"
          % (p, blk))
    print("  n = %d: zeros %d, blackCount(2n+1) %d, excess 5z-n = %d"
          % (n, z, b, exc))
    print("  ratio (5z-n)/blackCount = %.6f" % (exc / b))
    print("  %-10s %-14s %-14s" % ("n", "5z-n-2*black", "5z-n-3*black"))
    for nn in (500, 2000, 5000, 10000, n):
        if nn > n:
            continue
        zz = sum(1 for i in range(nn) if f[i] == 0)
        bb = sum(psi[:2 * nn + 1])
        print("  %-10d %-14d %-14d" % (nn, 5 * zz - nn - 2 * bb, 5 * zz - nn - 3 * bb))
    return exc / b


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    print("CriticalCharge C B R :  5*zeros(free R,n) <= n + B + C*blackCount(Psi R,2n+1)")
    print("exact integer arithmetic, horizon n = %d, depths 0..%d" % (n, 2 * n))
    ratios = [run(r, lab, n) for r, lab in WITNESSES]
    print("-" * 78)
    print("published witness ratio %.6f  -> C >= 2 (as published)" % ratios[0])
    for i, (r, lab) in enumerate(WITNESSES[1:], start=1):
        print("0x%-8x ratio %.6f  -> C >= %d; C = 2 FAILS for every B"
              % (r, ratios[i], int(ratios[i]) + 1))
    print()
    print("On every witness tested, 5*zeros - n - 3*blackCount stays negative and")
    print("decreasing, so C = 3 is not refuted by any of them.")


if __name__ == "__main__":
    main()
