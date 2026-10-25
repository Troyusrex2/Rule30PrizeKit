# -*- coding: utf-8 -*-
"""Search finite right halves for the extremal critical-charge ratio.

The critical-charge target is

    5*zeros(free R, n) <= n + B + C*blackCount(Psi R, 2*n+1).

For a fixed finite right half R the smallest natural C that can work, for ANY
additive allowance B, is governed by

    rho(R) = limsup_n  (5*zeros(free R,n) - n) / blackCount(Psi R, 2*n+1),

because a constant B cannot absorb a term growing linearly in n.  C = 1 is
already known false: the kernel-checked witness Rule30Ether.config 3 1 6 wall
has rho = 1.75.  This script measures rho over finite right halves to ask
whether C = 2 survives, and whether rho is bounded at all.

Stage 1 screens every support pattern inside positions 1..L at a small
horizon.  Stage 2 re-measures the leaders at a large horizon and reports the
ratio on a late window, so that a transient start cannot inflate it.

Usage:  python -I charge_ratio_search.py [L] [n_screen] [n_deep] [top]
"""
import sys
import time

sys.path.insert(0, ".")
from coupled_core import (WALL_C1, config, counts, excess, right_mask)  # noqa: E402

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass


def ratio_profile(rmask, n, window=4):
    """Ratios on a late window, plus the densities, for one right half."""
    z, b, f, psi = counts(rmask, n)
    out = {"n": n, "zeros": z, "black": b, "excess": excess(z, n)}
    out["ratio"] = (out["excess"] / b) if b else float("inf")
    out["zero_density"] = z / n
    out["black_density"] = b / (2 * n + 1)
    # second half window: the increments between n/2 and n
    h = n // 2
    zh = sum(1 for i in range(h) if f[i] == 0)
    bh = sum(psi[:2 * h + 1])
    dz, db = z - zh, b - bh
    out["tail_excess"] = 5 * dz - (n - h)
    out["tail_black"] = db
    out["tail_ratio"] = (out["tail_excess"] / db) if db else float("inf")
    return out


def screen(L, n):
    """Every support pattern inside positions 1..L, ranked by ratio."""
    rows = []
    for bits in range(1 << L):
        rmask = bits << 1                      # bit i of `bits` -> position i+1
        z, b, _, _ = counts(rmask, n)
        if b == 0:
            continue
        rows.append(((5 * z - n) / b, rmask))
    rows.sort(reverse=True)
    return rows


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    n_screen = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    n_deep = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    top = int(sys.argv[4]) if len(sys.argv) > 4 else 12

    ref = right_mask(config(3, 1, 6, WALL_C1))
    print("reference witness Rule30Ether.config 3 1 6 wall = 0x%x "
          "(0x%x with position 1 at bit 0)" % (ref, ref >> 1))
    rp = ratio_profile(ref, n_deep)
    print("  deep n=%d  excess=%d black=%d ratio=%.6f tail_ratio=%.6f"
          % (n_deep, rp["excess"], rp["black"], rp["ratio"], rp["tail_ratio"]))
    print()

    t0 = time.time()
    print("STAGE 1: screening all %d support patterns in positions 1..%d at n=%d"
          % (1 << L, L, n_screen))
    rows = screen(L, n_screen)
    print("  screened %d right halves with a nonzero sideways black count in %.1fs"
          % (len(rows), time.time() - t0))
    print("  best screen ratio %.6f, median %.6f, worst %.6f"
          % (rows[0][0], rows[len(rows) // 2][0], rows[-1][0]))
    print()

    print("STAGE 2: re-measuring the top %d at n=%d" % (top, n_deep))
    print("%-12s %10s %10s %10s %10s %10s %10s"
          % ("R (hex)", "screen", "excess", "black", "ratio", "tail", "blk dens"))
    best = None
    for scr, rmask in rows[:top]:
        p = ratio_profile(rmask, n_deep)
        print("0x%-10x %10.5f %10d %10d %10.5f %10.5f %10.5f"
              % (rmask, scr, p["excess"], p["black"], p["ratio"],
                 p["tail_ratio"], p["black_density"]))
        if best is None or p["tail_ratio"] > best[0]:
            best = (p["tail_ratio"], rmask, p)
    print()
    print("deep-window maximum tail ratio: %.6f at R = 0x%x" % (best[0], best[1]))
    print("C = 1 is refuted by any ratio > 1; C = 2 would be refuted by a ratio > 2.")
    print("verdict: C=2 %s on this sample"
          % ("REFUTED" if best[0] > 2 else "survives"))

    # How sparse can the sideways row get among the screened right halves?
    print()
    print("STAGE 3: minimum sideways black density at n=%d over the screened set"
          % n_deep)
    mins = []
    for _, rmask in rows[-top:] + rows[:top]:
        p = ratio_profile(rmask, n_deep)
        mins.append((p["black_density"], rmask, p["ratio"]))
    mins.sort()
    for d, rmask, r in mins[:6]:
        print("  R = 0x%-10x black density %.6f   ratio %.6f" % (rmask, d, r))


if __name__ == "__main__":
    main()
