"""Restrike forensics for Rule 30 (photograde aside).

A(t,x) = Rule 30 from the single seed, physical frame. B(t,x) = A(t+P,x) is the
"restrike": the same diagram shifted P steps in time. Column 0 eventually
P-periodic means A and B agree on column 0 forever after some T.

F001: the gating identity. If column 0 agrees at t and t+1, then
      D(t,-1) = D(t,1) AND NOT c0(t), where D = A XOR B.
F002: joint (columns 0 and 1) agreement runs, and the certificate that ends each
      one: the nearest left-side mismatch. Classify witnesses as rim (at or left of
      A's light-cone edge, t <= j) or interior.
"""
import json, sys
import numpy as np

TMAX_T, PMAX, LCAP = 4096, 512, 96
N = TMAX_T + PMAX + LCAP + 4
W = N + 2  # half-width; no boundary effect inside the cone


def evolve(n, seed=None):
    row = np.zeros(2 * W + 1, dtype=np.uint8)
    if seed is None:
        row[W] = 1
    else:  # control: fully random row (periodic ring), generic orbit
        row[:] = np.random.default_rng(seed).integers(0, 2, 2 * W + 1, dtype=np.uint8)
    H = np.empty((n, 2 * W + 1), dtype=np.uint8)
    for t in range(n):
        H[t] = row
        l = np.roll(row, 1); r = np.roll(row, -1)
        row = l ^ (row | r)
    return H


def col(H, x):
    return H[:, W + x]


def f001(H):
    c0, c1, cm = col(H, 0), col(H, 1), col(H, -1)
    n = len(c0)
    checked = mism = 0
    for P in range(1, PMAX + 1):
        t = np.arange(0, n - P - 1)
        ok = (c0[t] == c0[t + P]) & (c0[t + 1] == c0[t + 1 + P])
        lhs = cm[t] ^ cm[t + P]
        rhs = (c1[t] ^ c1[t + P]) & (1 - c0[t])
        checked += int(ok.sum()); mism += int(((lhs != rhs) & ok).sum())
    return {"P_range": [1, PMAX], "t_range": [0, n - 2], "instances_checked": checked, "mismatches": mism}


def f002(H):
    c0, c1 = col(H, 0), col(H, 1)
    runs = []
    for P in range(1, PMAX + 1):
        g = (c0[:TMAX_T + LCAP] == c0[P:P + TMAX_T + LCAP]) & (c1[:TMAX_T + LCAP] == c1[P:P + TMAX_T + LCAP])
        T = 1
        while T < TMAX_T:
            if g[T] and not g[T - 1]:
                L = 0
                while T + L < len(g) and g[T + L]:
                    L += 1
                runs.append((T, P, L))
                T += L
            else:
                T += 1
    runs.sort(key=lambda r: -r[2])
    top = runs[:2000]
    bound_violations = 0; rim = 0; detail = []
    for T, P, L in top:
        best = None
        for j in range(1, LCAP + 2):
            ts = np.arange(T, min(T + LCAP + 2 - j, H.shape[0] - P))
            if len(ts) == 0:
                break
            d = H[ts, W - j] ^ H[ts + P, W - j]
            hit = np.nonzero(d)[0]
            if len(hit):
                t = int(ts[hit[0]]); cost = t - T + j + 1
                if best is None or cost < best[0]:
                    best = (cost, t, j)
        if best is None or L > best[0] - 1:
            bound_violations += 1
        is_rim = best is not None and best[1] <= best[2]
        rim += int(is_rim)
        if len(detail) < 25:
            detail.append({"T": T, "P": P, "L": L, "Lstar": None if best is None else best[0],
                           "witness_t": None if best is None else best[1],
                           "witness_col": None if best is None else -best[2], "rim": is_rim})
    Ls = np.array([r[2] for r in runs])
    hist = {int(k): int((Ls == k).sum()) for k in range(10, int(Ls.max()) + 1)}
    tight = sum(1 for d in detail if d["Lstar"] == d["L"] + 1)
    return {"T_range": [1, TMAX_T], "P_range": [1, PMAX], "runs": len(runs),
            "max_L": int(Ls.max()), "L_hist_ge_10": hist, "mean_L": float(Ls.mean()),
            "L_quantiles_50_90_99_max": [float(np.quantile(Ls, q)) for q in (0.5, 0.9, 0.99)] + [int(Ls.max())],
            "longest_runs_examined": len(top), "certificate_violations": bound_violations,
            "rim_witnessed": rim, "interior_witnessed": len(top) - rim,
            "runs_with_L_greater_than_T": sum(1 for r in runs if r[2] > r[0]),
            "detail_top25": detail, "detail_tight_count": tight}


if __name__ == "__main__":
    which = sys.argv[1]
    if which == "F002C":  # control: same pipeline on 5 generic random orbits
        outs = [f002(evolve(N, seed=20261025 + k)) for k in range(5)]
        out = {"seeds": [20261025 + k for k in range(5)],
               "max_L": [o["max_L"] for o in outs], "mean_L": [o["mean_L"] for o in outs],
               "runs": [o["runs"] for o in outs],
               "L_hist_ge_10": [o["L_hist_ge_10"] for o in outs], "rim_witnessed": [o["rim_witnessed"] for o in outs],
               "certificate_violations": [o["certificate_violations"] for o in outs]}
        path = "evidence/F002_control_random_orbits.json"
        json.dump(out, open(path, "w"), indent=2); print(json.dumps(out)); sys.exit()
    H = evolve(N)
    out = f001(H) if which == "F001" else f002(H)
    path = "evidence/F001_gating_identity.json" if which == "F001" else "evidence/F002_restrike_runs.json"
    json.dump(out, open(path, "w"), indent=2)
    print(json.dumps({k: v for k, v in out.items() if k != "detail_top25"}))
