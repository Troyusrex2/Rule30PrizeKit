"""R2-02 photograde experiments. Physical frame: cell(t,x), x=0 is the seed
column, new(x) = f(cell(x-1), cell(x), cell(x+1)); Rule 30 f = l ^ (c | r).
Deterministic: all randomness from numpy default_rng(SEED)."""
import json, sys, numpy as np
from sklearn.linear_model import LogisticRegression
from sklearn.ensemble import HistGradientBoostingClassifier

SEED = 20261025
RULES = {30: lambda l, c, r: l ^ (c | r), 90: lambda l, c, r: l ^ r, 150: lambda l, c, r: l ^ c ^ r}
T = 4096            # time steps simulated
HALF = 64           # columns kept each side of 0 (enough for all windows; cone handled by padding)

def evolve(rule, init_bits, T=T):
    """init_bits: dict x->1. Returns array [T+1, 2*HALF+1] of columns -HALF..HALF.
    Simulated on a strip wide enough that no boundary effect reaches |x|<=HALF."""
    w = max([abs(x) for x in init_bits] + [0])
    W = HALF + T + w + 2
    row = np.zeros(2 * W + 1, dtype=np.uint8)
    for x in init_bits: row[W + x] = 1
    f = RULES[rule]; out = np.empty((T + 1, 2 * HALF + 1), dtype=np.uint8)
    for t in range(T + 1):
        out[t] = row[W - HALF: W + HALF + 1]
        l = np.roll(row, 1); r = np.roll(row, -1)
        row = f(l, row, r); row[0] = row[-1] = 0
    return out

def windows(hist, ts, cols, L):
    c0 = HALF
    return np.array([hist[t:t + L, [c0 + c for c in cols]].ravel() for t in ts], dtype=np.uint8)

def fit_eval(Xtr, ytr, Xte, yte, rng):
    res = {}
    for name, m in [("logistic", LogisticRegression(max_iter=2000)),
                    ("gboost", HistGradientBoostingClassifier(max_iter=200, random_state=0))]:
        m.fit(Xtr, ytr); res[name] = float((m.predict(Xte) == yte).mean())
        ys = rng.permutation(ytr); m.fit(Xtr, ys); res[name + "_shuffled_labels"] = float((m.predict(Xte) == yte).mean())
    return res

def random_init(rng, w=16):
    while True:
        b = rng.integers(0, 2, 2 * w + 1)
        if b.any(): return {x - w: 1 for x in range(2 * w + 1) if b[x]}

def exp_seed_signature(rng, n_neg_rows=40, L=8, cols=(-2, -1, 0, 1, 2)):
    """F001: can a two-sided coupled window (columns -2..2, L steps) tell the
    actual seed orbit from orbits of random finite rows, at held-out times?"""
    out = {}
    tr_t, te_t = range(64, 1024), range(1024, T - L)
    for rule in RULES:
        seed = evolve(rule, {0: 1})
        negs = [evolve(rule, random_init(rng)) for _ in range(n_neg_rows)]
        k_tr, k_te = 2000, 2000
        Ptr = windows(seed, rng.choice(tr_t, k_tr), cols, L); Pte = windows(seed, rng.choice(te_t, k_te), cols, L)
        half = n_neg_rows // 2
        Ntr = np.vstack([windows(negs[i], rng.choice(tr_t, k_tr // half), cols, L) for i in range(half)])
        Nte = np.vstack([windows(negs[i], rng.choice(te_t, k_te // half), cols, L) for i in range(half, n_neg_rows)])
        Xtr = np.vstack([Ptr, Ntr]); ytr = np.r_[np.ones(len(Ptr)), np.zeros(len(Ntr))]
        Xte = np.vstack([Pte, Nte]); yte = np.r_[np.ones(len(Pte)), np.zeros(len(Nte))]
        out[rule] = fit_eval(Xtr, ytr, Xte, yte, rng)
        out[rule]["density_seed"] = float(seed[1024:, HALF - 2:HALF + 3].mean())
        out[rule]["density_neg"] = float(np.mean([n[1024:, HALF - 2:HALF + 3].mean() for n in negs]))
    return out

def exp_driven_column(rng, n_rows=20, L=12):
    """F002: predict col1(t+1) from col0[t-L+1..t+1] and col1[t-L+1..t].
    col0(t+1) depends only on col-1,col0,col1 at t; col0(t+2) would leak col1(t+1)
    and is excluded. Local bound: col1(t+1) = col0(t) ^ (col1(t) | col2(t)), with
    col2 unseen. Compare the seed with random-row orbits and with the local bound."""
    out = {}
    tr_t, te_t = np.arange(L + 64, 2048), np.arange(2048, T - 2)
    def feats(h, ts):
        c0, c1 = h[:, HALF], h[:, HALF + 1]
        X = np.array([np.r_[c0[t - L + 1:t + 2], c1[t - L + 1:t + 1]] for t in ts], dtype=np.uint8)
        y = np.array([c1[t + 1] for t in ts]); return X, y
    def bound(h, ts):
        c0, c1 = h[:, HALF], h[:, HALF + 1]
        # Bayes-optimal using only the local rule and a fair guess for unseen col2
        det = c1[ts] == 1
        return float(det.mean() + 0.5 * (~det).mean())
    for rule in RULES:
        res = {}
        seed = evolve(rule, {0: 1})
        X, y = feats(seed, tr_t); Xt, yt = feats(seed, te_t)
        res["seed"] = fit_eval(X, y, Xt, yt, rng); res["seed"]["n_train"] = int(len(X))
        res["seed"]["majority_class_test"] = float(max(yt.mean(), 1 - yt.mean()))
        rows = [evolve(rule, random_init(rng)) for _ in range(n_rows)]
        X = np.vstack([feats(h, tr_t)[0] for h in rows[:n_rows // 2]]); y = np.concatenate([feats(h, tr_t)[1] for h in rows[:n_rows // 2]])
        Xt = np.vstack([feats(h, te_t)[0] for h in rows[n_rows // 2:]]); yt = np.concatenate([feats(h, te_t)[1] for h in rows[n_rows // 2:]])
        i = rng.choice(len(X), len(tr_t), replace=False); j = rng.choice(len(Xt), len(te_t), replace=False)
        res["random_rows_matched_n"] = fit_eval(X[i], y[i], Xt[j], yt[j], rng)
        res["random_rows_matched_n"]["n_train"] = int(len(i))
        out[rule] = res
    return out

def check_joint_periodicity_lemma(rule=30, T_=600):
    """F003 sanity: left-permutive reconstruction. Columns x and x+1 determine x-1 via
    l(t) = c(t+1) ^ (c(t) | r(t)). Verify on the actual Rule 30 seed for all t<T_."""
    h = evolve(30, {0: 1}, T_)
    bad = 0
    for x in range(-HALF + 1, HALF - 1):
        l, c, r = h[:, HALF + x - 1], h[:, HALF + x], h[:, HALF + x + 1]
        bad += int((l[:-1] != (c[1:] ^ (c[:-1] | r[:-1]))).sum())
    return {"columns_checked": 2 * HALF - 2, "times": T_, "mismatches": bad}

if __name__ == "__main__":
    rng = np.random.default_rng(SEED)
    which = sys.argv[1]
    res = {"F001": exp_seed_signature, "F002": exp_driven_column}.get(which, lambda r: check_joint_periodicity_lemma())(rng)
    print(json.dumps(res, indent=1))
