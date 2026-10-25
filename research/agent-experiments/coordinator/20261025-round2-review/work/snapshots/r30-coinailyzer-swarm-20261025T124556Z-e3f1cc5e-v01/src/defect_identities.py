"""Exact cross-column defect identities for Rule 30 from the single black cell.

Every check here is a finite computation on the actual single-seed orbit.
None of it is a proof; the identities are proved by hand in REPORT.md and the
numbers below only confirm that the hand derivation matches the real orbit.

Notation: D_x^P(t) = cell(t+P, x) XOR cell(t, x), the period-P defect field.
"""
import sys
from ca_core import evolve, rule_table, black_left_edge

T = 1200
PS = [1, 2, 3, 5, 7, 11, 14, 29, 64, 97]
ok = True


def report(name, passed, detail=""):
    global ok
    ok = ok and passed
    print(f"[{'PASS' if passed else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))


rows = evolve(T, 30)


def c(t, x):
    """cell(t,x) with the outside-the-cone zeros made explicit."""
    if t < 0 or t > T or x < -T or x > T:
        raise IndexError
    return rows[t][x + T + 1]


def D(P, x, t):
    return c(t + P, x) ^ c(t, x)


# --- A. the two boundary facts the argument rests on -------------------------
report("A1 left edge cell(t,-t)=1 for 0<=t<=%d" % T, black_left_edge(rows, T))
outside = all(c(t, x) == 0 for t in range(0, T + 1, 37) for x in range(-T, -t))
report("A2 cell(t,x)=0 for x < -t (light cone)", outside)

# --- B. left-permutive reconstruction ---------------------------------------
# cell(t, x-1) = cell(t+1, x) XOR (cell(t,x) OR cell(t,x+1))
bad = [(t, x) for t in range(T) for x in range(-(T - 1) + 1, T - 1)
       if c(t, x - 1) != (c(t + 1, x) ^ (c(t, x) | c(t, x + 1)))]
report("B  leftward reconstruction identity, all t<%d, all interior x" % T,
       not bad, f"{(T)*(2*T-3)} instances checked")

# --- C. unconditional defect recursion --------------------------------------
# D_{x-1}(t) = D_x(t+1) XOR [ (c(t+P,x) OR c(t+P,x+1)) XOR (c(t,x) OR c(t,x+1)) ]
n_c = 0
bad_c = []
for P in PS:
    for t in range(0, T - P - 1, 3):
        for x in range(-40, 41):
            lhs = D(P, x - 1, t)
            rhs = D(P, x, t + 1) ^ ((c(t + P, x) | c(t + P, x + 1)) ^ (c(t, x) | c(t, x + 1)))
            n_c += 1
            if lhs != rhs:
                bad_c.append((P, t, x))
report("C  unconditional defect recursion", not bad_c, f"{n_c} instances, {len(PS)} periods")

# --- D. defect locality (the sideways path step) -----------------------------
# D_{x-1}(t)=1  =>  D_x(t+1)=1 or D_x(t)=1 or D_{x+1}(t)=1
n_d = hits = 0
bad_d = []
for P in PS:
    for t in range(0, T - P - 1, 3):
        for x in range(-40, 41):
            if D(P, x - 1, t):
                hits += 1
                if not (D(P, x, t + 1) or D(P, x, t) or D(P, x + 1, t)):
                    bad_d.append((P, t, x))
            n_d += 1
report("D  defect locality step", not bad_d, f"{hits} live defects of {n_d} cells")

# --- E. masked transfer at depth 1 -------------------------------------------
# Hypothesis-local form: where D_0(t)=D_0(t+1)=0,  D_{-1}(t) = (1-c(t,0))*D_1(t)
n_e = bad_e = 0
nontrivial = 0
for P in PS:
    for t in range(0, T - P - 2):
        if D(P, 0, t) == 0 and D(P, 0, t + 1) == 0:
            n_e += 1
            pred = (1 - c(t, 0)) & D(P, 1, t)
            if D(P, -1, t) != pred:
                bad_e += 1
            if D(P, 1, t):
                nontrivial += 1
report("E  masked depth-1 identity on center-agreement times", bad_e == 0,
       f"{n_e} qualifying (P,t), {nontrivial} with a live column+1 defect")

# --- F. masked transfer at depth 2 -------------------------------------------
# where D_0(t)=0:            D_{-2}(t) = D_{-1}(t+1) XOR (1-c(t,0))*D_{-1}(t)
# where D_0(t..t+2)=0:       D_{-2}(t) = (1-c(t+1,0))*D_1(t+1) XOR (1-c(t,0))*D_1(t)
n_f1 = bad_f1 = n_f2 = bad_f2 = 0
for P in PS:
    for t in range(0, T - P - 3):
        if D(P, 0, t) == 0:
            n_f1 += 1
            if D(P, -2, t) != (D(P, -1, t + 1) ^ ((1 - c(t, 0)) & D(P, -1, t))):
                bad_f1 += 1
        if D(P, 0, t) == 0 and D(P, 0, t + 1) == 0 and D(P, 0, t + 2) == 0:
            n_f2 += 1
            rhs = ((1 - c(t + 1, 0)) & D(P, 1, t + 1)) ^ ((1 - c(t, 0)) & D(P, 1, t))
            if D(P, -2, t) != rhs:
                bad_f2 += 1
report("F1 depth-2 identity in terms of column -1", bad_f1 == 0, f"{n_f1} qualifying (P,t)")
report("F2 depth-2 identity in terms of column +1", bad_f2 == 0, f"{n_f2} qualifying (P,t)")

# --- G. light-cone defect ----------------------------------------------------
# D_{-m}(m-P) = 1 for every m >= P >= 1
bad_g = [(P, m) for P in PS for m in range(P, T - P) if D(P, -m, m - P) != 1]
report("G  light-cone defect D_{-m}(m-P)=1", not bad_g, f"{sum(T-2*P for P in PS)} instances")

# --- H. rule 90 contrast: the transfer is unmasked and linear ----------------
rows90 = evolve(400, 90)


def c90(t, x):
    return rows90[t][x + 401]


def D90(P, x, t):
    return c90(t + P, x) ^ c90(t, x)


bad_h = [(P, t, x) for P in (1, 2, 3, 7, 16) for t in range(0, 300) for x in range(-30, 31)
         if D90(P, x - 1, t) != (D90(P, x, t + 1) ^ D90(P, x + 1, t))]
report("H  rule 90 defect transfer is unmasked XOR", not bad_h,
       "D_{x-1}(t) = D_x(t+1) XOR D_{x+1}(t), 5 periods x 300 t x 61 x")

print("\nALL CHECKS PASS" if ok else "\nSOME CHECK FAILED")
sys.exit(0 if ok else 1)
