"""Evidence for F001: left/right periodicity asymmetry in Rule 30 from a single cell.

Measures, in the moving light-cone frame, the temporal period of a 12-cell window
sitting `depth` cells inside the left edge and inside the right edge.
Run: python probe_asymmetry.py          (stdlib only, ~10 s)
"""
N = 1400
row = [0] * (2 * N + 3)
row[N + 1] = 1
rows = []
for _ in range(1200):
    nxt = [0] * len(row)
    for i in range(1, len(row) - 1):
        l, c, r = row[i - 1], row[i], row[i + 1]
        nxt[i] = l ^ (c | r)          # Rule 30
    row = nxt
    rows.append(row)


def period(depth, side, w=12, lo=300, hi=700, maxp=400):
    """Smallest p<=maxp with the window constant under t -> t+p on [lo,hi); None if none."""
    f = []
    for t in range(hi + maxp + 2):
        r = rows[t]
        if side == "L":
            f.append(tuple(r[N + 1 - t - 1 + depth + k] for k in range(w)))
        else:
            f.append(tuple(r[N + 1 + t + 1 - depth - k] for k in range(w)))
    for p in range(1, maxp + 1):
        if all(f[i] == f[i + p] for i in range(lo, hi)):
            return p
    return None


if __name__ == "__main__":
    print("depth   left_period   right_period")
    for d in (1, 5, 10, 20, 40, 80, 160):
        print(f"{d:5d}   {str(period(d,'L')):11s}   {str(period(d,'R'))}")
