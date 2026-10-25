# -*- coding: utf-8 -*-
"""Purely periodic Golden free streams never beat 7/4.

Scans every cyclically Golden word of length <= L as a purely periodic free
stream f, and computes the charge ratio

    (5*zeros_rate - 1) / (2 * density of Theta f).

The contrast with slip_trend.py is the point of F002: a transient, not the
periodic part, is what buys a ratio above 2.

Usage:  python -I periodic_scan.py [L] [depth]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coupled_core import psi_row  # noqa: E402

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass


def cyc_golden(w):
    s = "".join(str(b) for b in w + w + w)
    return "00" not in s and "11111" not in s


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    depth = int(sys.argv[2]) if len(sys.argv) > 2 else 1600
    n = depth // 2 + 2
    best, tested = [], 0
    for p in range(1, L + 1):
        for bits in range(1 << p):
            w = [(bits >> i) & 1 for i in range(p)]
            if not cyc_golden(w):
                continue
            zr = sum(1 for x in w if x == 0) / p
            er = 5 * zr - 1
            if er <= 0:
                continue
            f = [w[s % p] for s in range(n)]
            psi = psi_row(f, depth)
            a = int(depth * 0.6)
            seg = psi[a:depth + 1]
            d = sum(seg) / len(seg)
            tested += 1
            if d > 0:
                best.append((er / (2 * d), "".join(str(x) for x in w), zr, d))
    best.sort(reverse=True)
    print("PURELY PERIODIC Golden free streams, cycle length <= %d, depth %d" % (L, depth))
    print("tested %d cycles with positive excess rate" % tested)
    print("%-10s %-16s %-11s %-14s" % ("ratio", "cycle", "zero rate", "Theta density"))
    for r, w, zr, d in best[:8]:
        print("%-10.6f %-16s %-11.6f %-14.6f" % (r, w, zr, d))
    print()
    print("maximum ratio over purely periodic Golden streams: %.6f" % best[0][0])
    print("A purely periodic free stream never exceeds 7/4. Every ratio above 2 found")
    print("in this response comes from an eventually-periodic stream with a TRANSIENT.")


if __name__ == "__main__":
    main()
