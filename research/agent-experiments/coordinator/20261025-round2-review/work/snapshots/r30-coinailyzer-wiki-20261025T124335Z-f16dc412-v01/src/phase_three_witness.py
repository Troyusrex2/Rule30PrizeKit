# -*- coding: utf-8 -*-
"""The alternating driver has TWO ether phases, and only one was used.

Rule30CriticalChargeOneCoreResearch proves `altCol t = ether 3 (t+1)` and
builds its witness as `Rule30Ether.config 3 1 6 wall`.  But ether column 3 is
`[false,true,false,true]`, which has period TWO in the phase, so

    ether 3 (t+1) = ether 3 (t+3) = altCol t

for every t.  Phase 3 represents the same alternating driver as phase 1.  The
published witness uses phase 1 only.  This script evaluates the phase-3
members of the same proved trap family:

    config 3 3 k ws,  (3+k) % 7 = 2,  (3, ws) in Rule30Ether.wallStates

and compares their critical-charge ratio against the phase-1 witness.

Usage:  python -I phase_three_witness.py [n]
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coupled_core import (WALL_C1, config, counts, ether, right_mask)  # noqa: E402

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

HERE = os.path.dirname(os.path.abspath(__file__))
WALLSTATES = [(p, b) for p, b in json.load(open(os.path.join(HERE, "wallstates.json")))]


def driver_check():
    """altCol t = ether 3 (t+1) = ether 3 (t+3), for every t mod 4."""
    ok1 = all((t % 2 == 0) == bool(ether(3, t + 1)) for t in range(400))
    ok3 = all((t % 2 == 0) == bool(ether(3, t + 3)) for t in range(400))
    print("altCol t == ether 3 (t+1) : %s" % ok1)
    print("altCol t == ether 3 (t+3) : %s" % ok3)
    print("so phases 1 and 3 of column 3 are the SAME alternating driver.")
    print("column 1 is then ether column 4 = %s, read at phase t+1 or t+3."
          % [ether(4, p) for p in range(4)])
    return ok1 and ok3


def period_of(seq, maxpre=60, maxper=60):
    for pre in range(maxpre):
        tail = seq[pre:]
        for p in range(1, maxper + 1):
            if len(tail) >= 4 * p and all(tail[i] == tail[i % p] for i in range(len(tail))):
                return pre, p
    return None


def report(rmask, n, label):
    z, b, f, psi = counts(rmask, n)
    exc = 5 * z - n
    pf = period_of(f[:200])
    pp = period_of(psi[1:400])
    line = ("%-34s zeros %-6d black %-6d excess %-6d ratio %.6f"
            % (label, z, b, exc, exc / b if b else float("inf")))
    print(line)
    print("      free %s... period %s | Psi(d>=1) %s... period %s"
          % ("".join(str(x) for x in f[:12]), pf,
             "".join(str(x) for x in psi[1:15]), pp))
    return exc / b if b else float("inf"), pf, pp


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2800
    n -= n % 14
    print("=== the two phases of the alternating driver ===")
    assert driver_check()
    print()

    print("=== phase 1: the published kernel-checked C=1 witness ===")
    r1 = right_mask(config(3, 1, 6, WALL_C1))
    base, _, _ = report(r1, n, "config 3 1 6 wall (0x%x)" % r1)
    print()

    print("=== phase 3: same trap family, same k, the 27 phase-3 wall states ===")
    best = None
    ratios = {}
    for idx, (ph, ws) in enumerate(WALLSTATES):
        if ph != 3:
            continue
        r = right_mask(config(3, 3, 6, ws))
        z, b, f, psi = counts(r, n)
        exc = 5 * z - n
        rat = exc / b if b else float("inf")
        ratios[idx] = (rat, r, ws)
        if best is None or rat > best[0]:
            best = (rat, r, ws, idx)
    vals = sorted(set(round(v[0], 6) for v in ratios.values()))
    print("  %d phase-3 wall states tested at n=%d; distinct ratios: %s"
          % (len(ratios), n, vals))
    rat, r, ws, idx = best
    report(r, n, "config 3 3 6 ws[%d] (0x%x)" % (idx, r))
    print()

    print("=== verdict ===")
    print("phase 1 ratio %.6f  ->  C must be at least %d" % (base, -(-base // 1)))
    print("phase 3 ratio %.6f  ->  C must be at least %d" % (rat, -(-rat // 1)))
    if rat > 2:
        print("C = 2 FAILS for the phase-3 witness, for every additive allowance B:")
        k = 1
        print("  the excess grows at 3/2 per free step while 2*blackCount grows at %.6f,"
              % (2 * (rat and 1.5 / rat)))
        print("  so 5*zeros - n - 2*blackCount -> +infinity.")
    print()
    print("=== scaling the same construction: larger k with (3+k) %% 7 == 2 ===")
    for k in (6, 13, 20, 27):
        rr = right_mask(config(3, 3, k, ws))
        z, b, f, psi = counts(rr, n)
        exc = 5 * z - n
        print("  k=%-3d support<=%-4d zeros %-6d black %-6d excess %-6d ratio %.6f"
              % (k, k + 13, z, b, exc, exc / b if b else float("inf")))


if __name__ == "__main__":
    main()
