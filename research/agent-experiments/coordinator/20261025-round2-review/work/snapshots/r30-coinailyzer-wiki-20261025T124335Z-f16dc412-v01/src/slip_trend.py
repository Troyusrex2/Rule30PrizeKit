# -*- coding: utf-8 -*-
"""Does one phase slip, pushed further out, make Theta f arbitrarily sparse?

The exhaustive prefix search finds that the sparsest reconstructed rows come
from an alternating free stream carrying a single PHASE SLIP: alternating up
to some index L, then alternating in the opposite parity.  Golden allows this
(it creates one `11`, and forbids only `00` and `11111`).

The pure alternating streams give Theta densities 3/7 and 6/7.  One slip at
L = 2 gives 5/14.  This script pushes the slip outwards and measures the
deep-window density of Theta f, to decide whether the implied critical-charge
ratio 1.5 / (2*density) stays bounded.

A falling density with no floor would mean NO uniform constant C can satisfy
    5*zeros(free R,n) <= n + B + C*blackCount(Psi R,2*n+1)
across right halves -- provided the streams are achievable (see achievable.py).
This script alone says nothing about achievability.

Usage:  python -I slip_trend.py [max_slip] [depth]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coupled_core import psi_row  # noqa: E402

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass


def slip_stream(L, n, start_phase=0):
    """Alternating, one phase slip at index L, then alternating again."""
    f = []
    for s in range(n):
        if s < L:
            f.append((s + start_phase) % 2)
        else:
            f.append((s + start_phase + 1) % 2)
    return f


def golden(f):
    s = "".join(str(b) for b in f)
    return "00" not in s and "11111" not in s


def deep_density(f, depth, lo=0.6):
    psi = psi_row(f, depth)
    a = int(depth * lo)
    seg = psi[a:depth + 1]
    return sum(seg) / len(seg)


def tail_period(psi, lo, maxp=200):
    tail = psi[lo:]
    for p in range(1, maxp + 1):
        if len(tail) >= 4 * p and all(tail[i] == tail[i % p] for i in range(len(tail))):
            return p, sum(tail[:p])
    return None, None


def main():
    maxL = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    depth = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    n = depth // 2 + 2
    print("one phase slip at index L, depth %d, density on the deep 40%%" % depth)
    print("%-5s %-8s %-12s %-10s %-22s" % ("L", "golden", "density", "ratio", "exact tail period"))
    best = None
    for L in range(0, maxL + 1):
        for ph in (0, 1):
            f = slip_stream(L, n, ph)
            if not golden(f[:80]):
                continue
            psi = psi_row(f, depth)
            a = int(depth * 0.6)
            seg = psi[a:depth + 1]
            d = sum(seg) / len(seg)
            p, blk = tail_period(psi, a)
            exact = ("period %d, %d black -> %.6f" % (p, blk, blk / p)) if p else "none <= 200"
            ratio = 1.5 / (2 * d) if d else float("inf")
            print("%-5d %-8s %-12.6f %-10.6f %-22s" % (L, "yes", d, ratio, exact))
            if best is None or ratio > best[0]:
                best = (ratio, L, ph, d, exact)
    print()
    print("maximum ratio %.6f at slip L=%d phase %d (density %.6f, %s)"
          % (best[0], best[1], best[2], best[3], best[4]))


if __name__ == "__main__":
    main()
