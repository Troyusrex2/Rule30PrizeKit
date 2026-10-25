"""Does ANY finite seed of a shared-structure rule give an eventually periodic
column with a NON-constant period?

The kit's two-column theorem (Rule30FiniteConfigs, after Jen 1986) holds for
every configuration with a leftmost black cell under three shared facts:
quiescence f(0,0,0)=0, black left edge f(0,0,1)=1, and left-permutivity.
Exactly four elementary rules have all three: 30, 90, 150, 210. At most one
column per orbit can then be eventually periodic. This sweep asks which
periods are actually REALIZED in the family, because a realized period is a
period the shared structure alone provably cannot exclude.

Bitwise rows (one Python int per row), so the box can be large.
A negative result is evidence about the search box, not a theorem.
"""
import json
from ca_core import rule_table

RULES = [30, 90, 150, 210]
W_MAX = 14          # seed widths 1..W_MAX, leftmost cell black
T = 900             # time prefix
MAXP = 32           # periods searched
MAXTR = 200         # transient allowed
NCOL = 24           # columns 0..NCOL-1 counted from the seed's leftmost cell
LEFTPAD = 4         # ... plus LEFTPAD columns to the left of it


def orbit_columns(n, bits, T):
    """Columns [-LEFTPAD, NCOL) of rule n from seed `bits`, as bytes objects."""
    tab = rule_table(n)
    W = 2 * T + len(bits) + 4
    mask = (1 << W) - 1
    base = T + 2                       # bit index of the seed's leftmost cell
    row = 0
    for i, b in enumerate(bits):
        if b:
            row |= 1 << (base + i)
    terms = [(p, q, r) for (p, q, r), v in tab.items() if v]
    nc = NCOL + LEFTPAD
    colmask = (1 << nc) - 1
    wins = [((row >> (base - LEFTPAD)) & colmask)]
    for _ in range(T):
        L = (row << 1) & mask
        C = row
        R = row >> 1
        nxt = 0
        for p, q, r in terms:
            nxt |= ((L if p else ~L) & (C if q else ~C) & (R if r else ~R))
        row = nxt & mask
        wins.append((row >> (base - LEFTPAD)) & colmask)
    return [bytes((w >> j) & 1 for w in wins) for j in range(nc)]


def ev_periods(col):
    L = len(col)
    return [P for P in range(1, MAXP + 1) if col[MAXTR + P:] == col[MAXTR:L - P]]


def main():
    found, n_orbits, n_cols = [], 0, 0
    for n in RULES:
        for w in range(1, W_MAX + 1):
            for mid in range(1 << (w - 1)):
                bits = [1] + [(mid >> i) & 1 for i in range(w - 1)]
                cols = orbit_columns(n, bits, T)
                n_orbits += 1
                for j, col in enumerate(cols):
                    x = j - LEFTPAD
                    n_cols += 1
                    ps = ev_periods(col)
                    if ps:
                        const = len(set(col[MAXTR:])) == 1
                        found.append({"rule": n, "seed": "".join(map(str, bits)), "col": x,
                                      "min_period": min(ps), "constant": const,
                                      "tail": "".join(str(c) for c in col[MAXTR:MAXTR + 40])})

    nonconst = [f for f in found if not f["constant"]]
    print(f"orbits swept: {n_orbits}   columns tested: {n_cols}")
    print(f"seeds leftmost-black width 1..{W_MAX}; columns {-LEFTPAD}..{NCOL-1}; "
          f"t<{T}; periods<={MAXP}; transient {MAXTR}")
    for n in RULES:
        fs = [f for f in found if f["rule"] == n]
        nc = [f for f in fs if not f["constant"]]
        per = sorted({f["min_period"] for f in fs})
        print(f"  rule {n:3d}: {len(fs):6d} eventually periodic columns, "
              f"{len(nc):3d} non-constant, minimal periods seen {per}")
    print(f"\nNON-CONSTANT eventually periodic columns in the whole family: {len(nonconst)}")
    for f in nonconst[:12]:
        print(f"  rule {f['rule']} seed {f['seed']} col {f['col']} "
              f"period {f['min_period']} tail {f['tail']}")
    json.dump({"params": {"rules": RULES, "w_max": W_MAX, "T": T, "maxp": MAXP,
                          "maxtr": MAXTR, "cols": [-LEFTPAD, NCOL - 1]},
               "orbits": n_orbits, "columns_tested": n_cols,
               "n_periodic_columns": len(found), "n_nonconstant": len(nonconst),
               "nonconstant_examples": nonconst[:200],
               "periodic_examples": found[:100]},
              open("../evidence/seed_sweep.json", "w"), indent=1)
    print("wrote ../evidence/seed_sweep.json")


if __name__ == "__main__":
    main()
