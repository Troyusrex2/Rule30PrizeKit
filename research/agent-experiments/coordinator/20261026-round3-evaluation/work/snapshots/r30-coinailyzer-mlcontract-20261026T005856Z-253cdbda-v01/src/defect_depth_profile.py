"""Does the period-P defect field thin out as you walk LEFT?

Background (my R2-05 response, F001): under the Problem 1 negation the
depth-1 transfer is a pure MASK,

    D_{-1}(t) = (1 XOR a(t,0)) AND D_{+1}(t),

so the depth-1 defect set is a SUBSET of column +1's -- it can only shrink.
Meanwhile the light cone forces D_{-m}(m-P) = 1 for EVERY m: the defect field
is non-empty arbitrarily far left. If shrinkage continued at every depth the
two would collide and Problem 1 would fall out. It does not continue: at
depth 2 the recursion is an XOR of two terms, which can CREATE a defect.

So the question is quantitative: measured on real orbits, does defect density
fall with leftward depth, and how fast? Rules 90 and 210 are the controls --
their centre column really is eventually periodic, and they have no OR, hence
no mask, so the mechanism predicts no decay there.
"""
import json
from ca_core import evolve, column

T = 2400
DEPTHS = list(range(0, 65, 4))
PS = [1, 2, 3, 5, 7, 11, 14, 29, 64]
out = {}

for rule in (30, 90, 210):
    rows = evolve(T, rule)
    cols = {x: column(rows, x, T) for x in range(-max(DEPTHS) - 2, 3)}
    per_p = {}
    for P in PS:
        prof = []
        for d in DEPTHS:
            c = cols[-d]
            # measure well inside the cone so the light-cone zeros do not
            # dominate: t from 2*max_depth to T-P
            lo = 2 * max(DEPTHS) + 10
            n = sum(c[t + P] ^ c[t] for t in range(lo, T - P))
            prof.append(round(n / (T - P - lo), 4))
        per_p[P] = prof
    out[rule] = per_p
    print(f"rule {rule}: defect density by leftward depth "
          f"(columns 0, -4, -8, ... -64), t in [{2*max(DEPTHS)+10},{T})")
    for P in PS:
        print(f"   P={P:3d}  " + " ".join(f"{v:.3f}" for v in per_p[P]))
    print()

print("Reading: a falling row would be the mask contracting the defect set.")
print("A flat row means the XOR term replenishes whatever the mask removes.")
json.dump({"T": T, "depths": DEPTHS, "periods": PS, "density": out},
          open("../evidence/defect_depth_profile.json", "w"), indent=1)
print("wrote ../evidence/defect_depth_profile.json")
