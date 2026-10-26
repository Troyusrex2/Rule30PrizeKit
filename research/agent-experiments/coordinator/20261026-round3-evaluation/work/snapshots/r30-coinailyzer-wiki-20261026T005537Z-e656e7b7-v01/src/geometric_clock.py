# -*- coding: utf-8 -*-
"""The off-the-wall idea, stated and then killed exactly.

IDEA.  `ScaleCharges` measures at cutoff(m,k) = (m+16)*(2^k - 1) and allows slack
floor(k/2), so the statement carries a doubling clock inside it.  A single phase slip in
the alternating free stream is the transient that buys a high charge ratio.  So let the
adversary slip ONCE PER DOUBLING -- slips at m, 2m, 4m, 8m, ... -- and he is defecting on
the statement's own clock, one fresh transient per scale at which he is measured.

OBSTRUCTION.  A slip flips the parity of the alternating tail, so the position at which
the next slip is Golden also flips: consecutive slips must sit at ODD gaps.  A doubling
schedule has gaps m, 2m, 4m, ..., and every gap after the first is even.  So no doubling
schedule of three or more slips is Golden, for ANY m -- and for even m not even two.
The free stream of a finite right half is always Golden
(`Rule30GoldenCoupledResearch.golden_free`), so the schedule is not merely unachieved,
it is unavailable.

This script checks the obstruction rather than asserting it: it enumerates doubling
schedules and the parity law itself.

Usage:  python -I geometric_clock.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from density_floor import golden, slip_stream  # noqa: E402

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass


def main():
    print("(1) the parity law.  Golden is two conditions and they split cleanly:")
    print("    no `00`  <=>  the first slip is at an even index (phase 0) and every")
    print("                  consecutive gap is ODD;")
    print("    no `11111` -- a SEPARATE restriction, not characterised here: slips at")
    print("                  2,3,4,5 have all-odd gaps and so pass the `00` law, yet the")
    print("                  stream carries `11111` and is not Golden.  Only the `00` law")
    print("                  is claimed exactly below, and only it is needed.")
    bad00 = bad = tested = 0
    for bits in range(1, 1 << 16):
        pos = [i for i in range(16) if (bits >> i) & 1]
        f = slip_stream(pos, 200)
        s = "".join(str(b) for b in f[:120])
        has00 = "00" in s
        law00 = not ((pos[0] % 2 == 0) and all((pos[i + 1] - pos[i]) % 2 == 1
                                               for i in range(len(pos) - 1)))
        tested += 1
        if has00 != law00:
            bad00 += 1
        if golden(f[:120]) != (not has00 and "11111" not in s):
            bad += 1
    print("    %d slip sets tested; `00` vs the parity law: %d mismatches" % (tested, bad00))
    print("    Golden vs (no 00 and no 11111): %d mismatches" % bad)
    print()
    print("    and the `11111` clause is NOT a run-length law on the slip set -- three")
    print("    candidate thresholds, each tested over the same 65,535 sets:")
    for thr in (4, 5, 6):
        miss = 0
        for bits in range(1, 1 << 16):
            pos = [i for i in range(16) if (bits >> i) & 1]
            s = "".join(str(b) for b in slip_stream(pos, 200)[:120])
            run, hit = 1, False
            for i in range(1, len(pos)):
                run = run + 1 if pos[i] - pos[i - 1] == 1 else 1
                if run >= thr:
                    hit = True
            if ("11111" in s) != hit:
                miss += 1
        print("      run >= %d : %d mismatches" % (thr, miss))
    print()

    print("(2) doubling schedules m*2^j, j = 0..k-1, against the law")
    print("  %-5s %-3s %-30s %-8s" % ("m", "k", "positions", "Golden"))
    any_golden3 = []
    for m in range(1, 41):
        for k in (2, 3, 4, 5):
            pos = [m * (2 ** j) for j in range(k)]
            f = slip_stream(pos, 4 * pos[-1] + 200)
            g = golden(f[:2 * pos[-1] + 60])
            if k <= 3 or g:
                print("  %-5d %-3d %-30s %-8s" % (m, k, pos, "yes" if g else "no"))
            if g and k >= 3:
                any_golden3.append((m, k))
    print()
    print("  doubling schedules of 3 or more slips that are Golden: %s"
          % (any_golden3 if any_golden3 else "NONE"))
    print()
    print("(3) what survives of the idea")
    print("  The clock is the wrong object to put a slip on, but the SLACK side of the")
    print("  ScaleCharges statement is untouched by this: floor(k/2) grows with k while a")
    print("  single slip contributes one bounded transient, so the slack is not what the")
    print("  adversary is fighting.  The fight is over the eventual DENSITY of Theta f,")
    print("  which is what `density_floor.py` measures.")


if __name__ == "__main__":
    main()
