# -*- coding: utf-8 -*-
"""Where the critical-charge ratio actually comes from.

Both sides of

    5*zeros(free R, n) <= n + B + C*blackCount(Psi R, 2*n+1)

are functions of the SINGLE free stream f = free R, because
Psi R = Theta (free R) and free R k = zrow (Psi R) (2k+1) 1.  The right half
R enters only by deciding which streams f are achievable.

free R is always Golden (Rule30GoldenCoupledResearch.golden_free), so it has
no `00` and its zero density is at most 1/2, with equality exactly when f is
eventually alternating.  The excess 5*zeros(f,n) - n therefore grows at a rate
of at most 3/2, attained precisely on the eventually-alternating streams.

So the extremal ratio is decided by one question: among eventually-alternating
streams, how SPARSE can the reconstructed row Theta f be?  This script answers
it by exhaustive search over the finite prefix that precedes the alternating
tail, and reports the density of Theta f on a deep window.

Usage:  python -I prefix_density.py [prefix_len] [depth]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coupled_core import psi_row  # noqa: E402

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass


def golden_ok(bits):
    """Golden: no 00 and no 11111."""
    s = "".join(str(b) for b in bits)
    return "00" not in s and "11111" not in s


def stream(prefix, n, phase):
    """prefix, then alternating with f(s) = (s + phase) % 2 from s = len(prefix)."""
    f = list(prefix)
    for s in range(len(prefix), n):
        f.append((s + phase) % 2)
    return f[:n]


def tail_density(f, depth, lo_frac=0.5):
    """Black density of Theta f over the DEEP half of depths 0..depth."""
    psi = psi_row(f, depth)
    lo = int(depth * lo_frac)
    seg = psi[lo:depth + 1]
    return sum(seg) / len(seg), psi


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    depth = int(sys.argv[2]) if len(sys.argv) > 2 else 2800
    n = depth // 2 + 2

    print("Deep-window black density of Theta f for f = <prefix> + alternating tail")
    print("depth = %d, density measured on the deep half, prefixes up to length %d"
          % (depth, L))
    print()

    results = []
    for plen in range(0, L + 1):
        for bits in range(1 << plen):
            prefix = [(bits >> i) & 1 for i in range(plen)]
            for phase in (0, 1):
                f = stream(prefix, n, phase)
                if not golden_ok(f[:min(len(f), 60)]):
                    continue
                d, _ = tail_density(f, depth)
                results.append((d, plen, tuple(prefix), phase))
    results.sort()

    print("%-10s %-6s %-22s %-6s %-10s" % ("density", "len", "prefix", "phase", "ratio"))
    seen = set()
    shown = 0
    for d, plen, prefix, phase in results:
        key = round(d, 6)
        if key in seen:
            continue
        seen.add(key)
        ratio = 1.5 / (2 * d) if d else float("inf")
        print("%-10.6f %-6d %-22s %-6d %-10.6f"
              % (d, plen, "".join(str(b) for b in prefix) or "(empty)", phase, ratio))
        shown += 1
        if shown >= 12:
            break
    print()
    dmin = results[0][0]
    print("minimum deep-window density over %d streams: %.6f" % (len(results), dmin))
    print("maximum implied charge ratio 1.5 / (2*density) = %.6f" % (1.5 / (2 * dmin)))
    print("(the pure alternating streams give %.6f and %.6f)"
          % tuple(sorted({round(tail_density(stream([], n, ph), depth)[0], 6)
                          for ph in (0, 1)})))


if __name__ == "__main__":
    main()
