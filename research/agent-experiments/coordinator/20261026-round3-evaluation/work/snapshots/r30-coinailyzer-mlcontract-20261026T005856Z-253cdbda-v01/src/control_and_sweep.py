"""Control first: the real single-seed orbit MUST survive the same checker.
Then: how wide can a period-P centre survive before the constraints kill it?"""
import json
from ca_core import evolve, column
from sideways_sat_count import survivors

T = 400
rows = evolve(T, 30)
col0 = column(rows, 0, T)
col1 = column(rows, 1, T)


def check_real(N):
    """Run the identical constraint walk on the ACTUAL col0/col1 prefixes."""
    prev2 = col1[:N]
    prev1 = col0[:N]
    for d in range(1, N):
        width = min(len(prev1) - 1, len(prev2))
        if width <= 0:
            break
        cur = [prev1[t + 1] ^ (prev1[t] | prev2[t]) for t in range(width)]
        for t in range(width):
            if t < d and cur[t] != 0:
                return False, (d, t, "expected void")
            if t == d and cur[t] != 1:
                return False, (d, t, "expected black edge")
        prev2, prev1 = prev1, cur
    return True, None


print("CONTROL: the true rule 30 orbit against the same constraints")
bad = None
for N in range(4, 200):
    ok, why = check_real(N)
    if not ok:
        bad = (N, why)
        break
print("  survives every N in 4..199:", bad is None, "" if bad is None else f"FAILED at {bad}")
print("  (if this said False the checker would be wrong and everything below void)")
print()
print("  true centre prefix :", "".join(map(str, col0[:16])))
print("  true column+1 prefix:", "".join(map(str, col1[:16])))
print()

print("SWEEP: widest N at which SOME period-P centre word still has a solution")
res = {}
for P in range(1, 11):
    best, best_pat, alive_at_cap = 0, None, []
    for pat in range(1 << P):
        pattern = [(pat >> i) & 1 for i in range(P)]
        last_alive = 0
        for N in range(4, 23):
            c, _ = survivors(P, pattern, N)
            if c == 0:
                break
            last_alive = N
        else:
            alive_at_cap.append("".join(map(str, pattern)))
        if last_alive > best:
            best, best_pat = last_alive, "".join(map(str, pattern))
    res[P] = {"widest_surviving_N": best, "word": best_pat,
              "still_alive_at_cap_22": alive_at_cap}
    cap = f"  STILL ALIVE at the N=22 cap: {alive_at_cap}" if alive_at_cap else ""
    print(f"  P={P:2d}: widest surviving N = {best:2d}  (word {best_pat}){cap}")

json.dump({"control_passes": bad is None, "sweep": res},
          open("../evidence/control_and_sweep.json", "w"), indent=1)
print("\nwrote ../evidence/control_and_sweep.json")
