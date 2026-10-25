"""How loose is a logarithmic defect rate, and what caps it?

Theorem B of the report: if column 0 is P-periodic from time T, the period-P
defect count of column +1 up to time t is at least log2(t) - O(1). Its
hypothesis is false for rule 30 (that is Problem 1), so the bound cannot be
tested there. The other three members of the shared-structure family
{30,90,150,210} -- quiescent, black left edge, left-permutive -- all DO have an
eventually periodic centre column, so each is an orbit where every step of the
argument applies and the truth can be measured. Whatever rate such an orbit
realizes caps any rate provable from the shared facts alone.
"""
import json
import math
from seed_sweep import orbit_columns, LEFTPAD

T = 16384
P = 1
out = {}

print(f"single black cell, t < {T}, period P={P}\n")
for n in (90, 150, 210):
    cols = orbit_columns(n, [1], T)
    centre, col1, colm1 = cols[LEFTPAD], cols[LEFTPAD + 1], cols[LEFTPAD - 1]
    assert len(set(centre[1:])) == 1, n
    value = centre[1]
    D1 = [col1[t + P] ^ col1[t] for t in range(T - P)]
    Dm1 = [colm1[t + P] ^ colm1[t] for t in range(T - P)]
    blacks = [t for t in range(T) if col1[t]]
    pow2 = blacks == [2 ** k - 1 for k in range(1, 20) if 2 ** k - 1 < T]
    # Theorem B's conclusion, checked directly on this orbit
    bad = [m for m in range(1 + P, T // 2)
           if not any(D1[s] for s in range(m - P, min(2 * m - P, T - P)))]
    cum = []
    run = 0
    for t in range(T - P):
        run += D1[t]
        if t in (100, 1000, 10000, T - P - 1):
            cum.append((t, run, run / math.log2(t)))
    out[n] = {"centre_constant_value": value, "col1_black_times_are_2^k-1": pow2,
              "transfer_identity_Dm1_eq_D1": all(Dm1[t] == D1[t] for t in range(1, T - P)),
              "theoremB_conclusion_holds": not bad,
              "defect_density": sum(D1) / (T - P),
              "cumulative": [{"t": t, "N1": n1, "N1_over_log2t": r} for t, n1, r in cum]}
    print(f"rule {n}: centre column constant {value} from t=1")
    print(f"  D_(-1) = D_(+1) for every t >= 1: {out[n]['transfer_identity_Dm1_eq_D1']} "
          f"(no OR mask outside rule 30)")
    print(f"  Theorem B conclusion holds on this orbit: {out[n]['theoremB_conclusion_holds']}")
    print(f"  column +1 black exactly at t = 2^k - 1: {pow2}")
    print(f"  defect density of column +1: {out[n]['defect_density']:.4f}")
    print("     t      N_1(t)   N_1/log2 t")
    for t, n1, r in cum:
        print(f"   {t:6d}  {n1:8d}   {r:8.2f}")
    print()

print("Reading:")
print("  * rules 90 and 210 realize a periodic centre whose column +1 carries only")
print("    ~2*log2(t) defects, so NO rate better than O(log t) is provable from the")
print("    shared facts alone. The logarithm the defect-path argument stops at is a")
print("    real ceiling for that class of argument, not a slack step.")
print("  * both of those witnesses have an eventually WHITE centre. Rule 30 is")
print("    entitled to exclude that case (the kit proves no column is eventually")
print("    constant), and the only remaining witness, rule 150, has a constant BLACK")
print("    centre and a defect density of order 1. So once the hypothetical centre is")
print("    known to be non-constant, the family caps nothing: a positive-density")
print("    defect rate is not excluded by any sibling rule. A rate argument has to")
print("    consume both the zeros and the ones of the hypothetical centre.")

json.dump({"T": T, "P": P, "rules": out}, open("../evidence/rate_calibration.json", "w"), indent=1)
print("\nwrote ../evidence/rate_calibration.json")
