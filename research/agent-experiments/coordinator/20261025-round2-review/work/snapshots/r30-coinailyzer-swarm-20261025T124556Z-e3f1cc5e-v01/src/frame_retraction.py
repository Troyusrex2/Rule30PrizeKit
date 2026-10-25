"""Moving frame versus fixed columns: why my round-1 measurement did not say
what I claimed it said.

Round 1 (r30-coinailyzer-swarm-20261024T214719Z-1bf7da5f-v01, F001) measured a
12-cell window at a fixed DEPTH inside each light-cone edge and found the left
side temporally periodic to depth 160. That window travels leftwards at one
cell per step. Problem 1 is about a FIXED column. This script measures both and
locates the boundary that separates them.
"""
import json
from ca_core import evolve, column, eventual_period

T = 4000
rows = evolve(T, 30)


def cell(t, x):
    return rows[t][x + T + 1]


def win_period(depth, side, t0, t1, maxp=400, width=12):
    """Temporal period of a `width`-cell window at `depth` inside the moving
    light-cone edge: positions -t+depth (left) or t-depth (right)."""
    seqs = []
    for t in range(t0, t1):
        base = (-t + depth) if side == "left" else (t - depth - width + 1)
        seqs.append(tuple(cell(t, base + k) for k in range(width)))
    # require at least P genuine comparisons, so a period as long as the
    # sample is never accepted vacuously (the round-1 probe did not do this)
    for P in range(1, min(maxp, len(seqs) // 2) + 1):
        if all(seqs[i] == seqs[i + P] for i in range(len(seqs) - P)):
            return P
    return None


print("A. round-1 moving-frame table, recomputed (t in [300,700), periods <= 200,")
print("   a period being accepted only on at least P real comparisons)")
print("   depth   left   right")
moving = {}
for d in (1, 5, 10, 20, 40, 80, 160):
    l = win_period(d, "left", 300, 700, maxp=200)
    r = win_period(d, "right", 300, 700, maxp=200)
    moving[d] = (l, r)
    print(f"   {d:5d}  {str(l):>5}  {str(r):>5}")

print("\nB. the same question for FIXED columns (t in [1000,4000), periods <= 400,")
print("   transient up to 500) -- the quantity Problem 1 is about")
fixed = {}
for x in (-160, -80, -20, -5, -1, 0, 1, 5, 20, 80, 160):
    col = column(rows, x, T)[1000:]
    ep = eventual_period(col, 400, 500)
    fixed[x] = ep
    print(f"   column {x:5d}: {'period ' + str(ep[1]) if ep else 'no period <= 400'}")

print("")
print("C. where the regular left region ends. The moving-frame period is itself")
print("   depth dependent (4 near the edge, then 8, then 16), so the boundary is")
print("   the largest depth whose 12-cell window still has SOME period <= 64 over")
print("   200 steps; found by binary search on depth.")


def mv_period(d, t0, span=200, maxp=64, width=12):
    seqs = [tuple(cell(t, -t + d + k) for k in range(width)) for t in range(t0, t0 + span)]
    return next((P for P in range(1, maxp + 1)
                 if all(seqs[i] == seqs[i + P] for i in range(len(seqs) - P))), None)


bs = []
for t0 in (1000, 1500, 2000, 2500, 3000, 3700):
    lo, hi = 0, t0 - 20
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mv_period(mid, t0) is not None:
            lo = mid
        else:
            hi = mid - 1
    bs.append((t0, lo, lo / t0, -t0 + lo))
    print(f"   t={t0:5d}  boundary depth {lo:5d}  depth/t {lo/t0:.3f}  "
          f"at column x={-t0+lo:+6d}  window period {mv_period(lo, t0)}")
speed = sum(1 - b[2] for b in bs) / len(bs)
print("")
print(f"   The regular wedge is x <= -c*t with c = {speed:.3f} (the Rule 30 left")
print("   boundary speed, about 0.25 in the literature). A FIXED column x=-k is")
print(f"   inside the wedge only while t <= k/{speed:.3f}; after that it is in the")
print("   chaotic region forever. That is why B finds no fixed-column period while")
print("   A finds a moving-window period at every depth: the round-1 measurement")
print("   tracked a window that outruns every fixed column.")

json.dump({"T": T, "moving_frame": {str(k): v for k, v in moving.items()},
           "fixed_columns": {str(k): v for k, v in fixed.items()},
           "boundary_depths": bs, "boundary_speed_estimate": speed},
          open("../evidence/frame_retraction.json", "w"), indent=1)
print("\nwrote ../evidence/frame_retraction.json")
