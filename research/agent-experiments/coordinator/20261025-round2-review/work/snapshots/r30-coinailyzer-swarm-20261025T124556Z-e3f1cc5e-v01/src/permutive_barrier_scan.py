"""Which elementary rules share every structural fact the sideways/light-cone
argument uses, and which of those have an eventually periodic center column?

Shared facts used by the Jen-style argument (kit: Rule30FiniteConfigs):
  (i)   f(0,0,0) = 0            quiescent, so the orbit stays finitely supported
  (ii)  f(0,0,1) = 1            the left light-cone edge cell(t,-t) is black
  (iii) f(0,q,r) != f(1,q,r)    left-permutive, so columns x-1 is reconstructible
                                from columns x (times t, t+1) and x+1 (time t)
Any rule with (i)-(iii) admits the same proof that no two distinct columns are
both eventually periodic. A rule in that family whose CENTER column IS
eventually periodic is therefore a witness that (i)-(iii) cannot prove
Problem 1 -- and the period it realizes is the part of the all-period gap
that the shared structure provably cannot close.

Periodicity here is a finite search over a prefix, reported as such.
"""
import json
from ca_core import rule_table, evolve, column, is_left_permutive, black_left_edge, eventual_period

T = 3000
MAXP = 128
MAXTR = 600

family, witnesses, rows_out = [], [], []
for n in range(256):
    tab = rule_table(n)
    if tab[(0, 0, 0)] != 0 or tab[(0, 0, 1)] != 1 or not is_left_permutive(n):
        continue
    family.append(n)
    rows = evolve(T, n)
    assert black_left_edge(rows, T), n
    centre = column(rows, 0, T)
    ep = eventual_period(centre, MAXP, MAXTR)
    const = len(set(centre[200:])) == 1
    col1 = column(rows, 1, T)
    ep1 = eventual_period(col1, MAXP, MAXTR)
    rows_out.append({"rule": n, "centre_eventual_period": ep, "centre_constant_after_200": const,
                     "col1_eventual_period": ep1,
                     "centre_prefix": "".join(str(b) for b in centre[:40])})
    if ep is not None:
        witnesses.append((n, ep, const))

print(f"left-permutive, quiescent, black-left-edge family: {len(family)} rules")
print(f"  {family}")
print(f"\ncentre column eventually periodic within t<{T}, P<={MAXP}, transient<={MAXTR}:")
for n, ep, const in witnesses:
    kind = "CONSTANT" if const else "NON-CONSTANT"
    print(f"  rule {n:3d}: transient {ep[0]:4d}, period {ep[1]:3d}  [{kind}]")
nonconst = [w for w in witnesses if not w[2]]
print(f"\nnon-constant periodic-centre witnesses: {len(nonconst)}")
for n, ep, _ in nonconst:
    rows = evolve(600, n)
    print(f"  rule {n}: centre t=0..59 = " + "".join(str(b) for b in column(rows, 0, 600)[:60]))
print("\ncolumn +1 eventual period in the same window (expected None where the "
      "centre is periodic -- the two-column theorem):")
for r in rows_out:
    if r["centre_eventual_period"] is not None:
        print(f"  rule {r['rule']:3d}: col+1 -> {r['col1_eventual_period']}")

json.dump({"search": {"T": T, "max_period": MAXP, "max_transient": MAXTR},
           "family": family, "rows": rows_out},
          open("../evidence/permutive_family_scan.json", "w"), indent=1)
print("\nwrote ../evidence/permutive_family_scan.json")
