"""F003: finite ingredients of the unit-scale obstruction for readers that
absorb only after leaving the language of finitely many periodic
backgrounds (e.g. the round-two 1,110-state union reader, which RETAINS
the period-seven background and so is outside the generic barrier).

Input: the 1,110-state transition table T rebuilt by the coordinator's own
left_multi_vacuum_reader.build() (copied byte-for-byte into a scratch dir;
its own built-in controls passed), saved as T1110.npy, plus its 14
background patterns (pats.json).

Checks (exact bit computations; finite bounds stated in the output):
 (P) pump families for the sink-cost equalities.  For Y in {1^inf,
     (10000000)^inf} find a periodic Y' with next(Y'^inf) = Y^inf, build
     P_n = prefix40(phase) + 0^30 + Y'^n + [1],  R_n = next(P_n),
     S_n = next(R_n), n = 1..NMAX, and check: R_n canonical with black
     head, 13-double-step guard with the expected stream for R_n and S_n,
     the reader is in the sink after the white run in BOTH R_n and S_n, and
     the sink-letter tallies are affine in n with the per-period tallies of
     Y (in R_n) and next(Y) (in S_n).
 (O) a long-lived Golden orbit.  f = Fibonacci word with A->01, B->011.
     w = canonical truncation of Theta(f); w_j = next^j(w).  For j <= J:
     guard ok with stream sigma^j f, prefix of w_j equals Theta(sigma^j f),
     reader in the sink after <= p0 cells.
 (X) exhaustive factor check: for EVERY bit-factor g of f of length q the
     Theta prefix (which depends only on g) drives the reader to the sink;
     this makes the absorption bound uniform in j.
"""
import json, sys
import numpy as np
from zbl import next2, col1, strip

T = np.load(sys.argv[1]); pats = json.load(open(sys.argv[2]))
sink = [s for s in range(len(T)) if T[s, 0] == s and T[s, 1] == s]
assert len(sink) == 1
sink = sink[0]


def run(w):
    s = 0; pos = None
    for i, x in enumerate(w):
        s = int(T[s, x])
        if s == sink and pos is None:
            pos = i + 1
    return s, pos


def bg_bits(p, n):
    a = p['left_bits']; mu = p['transient']; per = p['period']
    return [a[d] if d < len(a) else a[mu + (d - mu) % per] for d in range(n)]


out = {"reader_states": int(len(T)), "sink": sink}
out["max_white_run_in_backgrounds"] = max(
    max(len(r) for r in ''.join(map(str, bg_bits(p, 2000))).split('1')) for p in pats)


def theta(f, n):
    """depths 1..n of the constrained row whose free bits are f."""
    col = [1 if t % 2 == 0 else f[t // 2] for t in range(n + 1)]   # times 0..n: uses f[0..n//2]
    prev = [0] * len(col); row = []
    while len(row) < n:
        row.append(col[0])
        prev, col = col, [col[j + 1] ^ (col[j] | prev[j]) for j in range(len(col) - 1)]
    return row


def stream_ok(w, stream, H=13):
    c = col1(w, 2 * H + 1)
    return all(c[2 * i] == 1 for i in range(H + 1)) and all(c[2 * i + 1] == stream[i] for i in range(H))


# ---------------- (P) pump families ----------------
E7 = [1, 1, 0, 0, 0, 0, 1]
ether = lambda n: [E7[i % 7] for i in range(n)]
# phase prefixes from the actual orbit of the period-seven row:
# Q1 = next(ether) phase: its step has free bit 1, so next(Q1...) has previous bit 1
# Q0 = ether phase: its step has free bit 0, so next(Q0...) has previous bit 0
Q0 = ether(40)
Q1 = next2(ether(60))[:40]
assert col1(ether(60), 2)[1] == 0 and col1(next2(ether(60)), 2)[1] == 1
assert theta([0, 1] * 60, 40) == Q0 and theta([1, 0] * 60, 40) == Q1


def bulk_next(y):
    """one period of next applied to the periodic configuration y^inf."""
    p = len(y); big = y * 8
    return next2(big)[3 * p:4 * p]   # same depths: the bulk double step has no index shift


def periodic_preimage(y, maxper=16):
    p = len(y)
    for per in range(p, maxper + 1, p):
        target = y * (per // p)
        for code in range(1 << per):
            x = [(code >> i) & 1 for i in range(per)]
            if bulk_next(x) == target:
                return x
    return None


def tally(w, a):
    seg = w[a:]
    return seg.count(0), seg.count(1)


fam = []
NMAX = 40
for name, Y in [("zeros", [0]), ("ones", [1]), ("single_one_period8", [1, 0, 0, 0, 0, 0, 0, 0])]:
    Yp = periodic_preimage(Y)
    assert Yp is not None, name
    FY = bulk_next(Y)
    for phase, Q, stream_R, stream_S in [(1, Q1, [0, 1] * 7, [1, 0] * 7), (0, Q0, [1, 0] * 7, [0, 1] * 7)]:
        recs = []
        for n in range(1, NMAX + 1):
            P = Q + [0] * 30 + Yp * n + [1]
            R = next2(P); S = next2(R)
            assert R[0] == 1 and R[-1] == 1 and S[0] == 1 and S[-1] == 1
            _, pR = run(R); _, pS = run(S)
            recs.append({"n": n, "safe_R": stream_ok(R, stream_R), "safe_S": stream_ok(S, stream_S),
                         "pR": pR, "pS": pS, "tR": tally(R, pR), "tS": tally(S, pS)})
        assert all(r["safe_R"] and r["safe_S"] for r in recs)
        assert all(r["pR"] is not None and r["pR"] <= 70 and r["pS"] is not None and r["pS"] <= 70 for r in recs)
        dR = sorted({(b["tR"][0] - a["tR"][0], b["tR"][1] - a["tR"][1]) for a, b in zip(recs[4:], recs[5:])})
        dS = sorted({(b["tS"][0] - a["tS"][0], b["tS"][1] - a["tS"][1]) for a, b in zip(recs[4:], recs[5:])})
        per = len(Yp)
        expR = (per // len(Y) * Y.count(0), per // len(Y) * Y.count(1))
        expS = (per // len(Y) * FY.count(0), per // len(Y) * FY.count(1))
        assert dR == [expR] and dS == [expS], (name, phase, dR, dS, expR, expS)
        fam.append({"family": name, "Y": Y, "Y_preimage_period": Yp, "next_Y_one_period": FY,
                    "R_previous_free_bit": phase, "R_next_free_bit": 1 - phase,
                    "n_checked": [1, NMAX], "guard13_ok_R_and_S": True,
                    "sink_positions_R": sorted({r["pR"] for r in recs}),
                    "sink_positions_S": sorted({r["pS"] for r in recs}),
                    "sink_tally_increment_per_n_R(zeros,ones)": expR,
                    "sink_tally_increment_per_n_S(zeros,ones)": expS})
out["pump_families"] = fam

# ---- exact certificate: the pump slopes force all four sink costs equal ----
# c = sink costs of C1 (phase 1 energy), d = sink costs of C0.  A phase-1 row R
# (next bit 0) requires E0(S_n) <= E1(R_n) - 1 for all n, so its slope satisfies
# d.tS - c.tR <= 0; a phase-0 row requires c.tS - d.tR <= 0.
from fractions import Fraction as Fr
ineq = {}
for f_ in fam:
    tR = f_["sink_tally_increment_per_n_R(zeros,ones)"]; tS = f_["sink_tally_increment_per_n_S(zeros,ones)"]
    if f_["R_previous_free_bit"] == 1:   # coefficients on (c0,c1,d0,d1)
        ineq[f_["family"], 1] = (-tR[0], -tR[1], tS[0], tS[1])
    else:
        ineq[f_["family"], 0] = (tS[0], tS[1], -tR[0], -tR[1])
def comb(*pairs):
    v = [Fr(0)] * 4
    for k, m in pairs:
        for i in range(4): v[i] += Fr(m) * ineq[k][i]
    return tuple(v)
Z1, Z0 = ("zeros", 1), ("zeros", 0); O1, O0 = ("ones", 1), ("ones", 0)
S1, S0 = ("single_one_period8", 1), ("single_one_period8", 0)
cert = {
  "d0-c0<=0": (comb((Z1, 1)), (-1, 0, 1, 0)),
  "c0-d0<=0": (comb((Z0, 1)), (1, 0, -1, 0)),
  "c0-d1<=0": (comb((O0, Fr(1, 3))), (1, 0, 0, -1)),
  "d1-c0<=0": (comb((S0, Fr(1, 8)), (S1, Fr(3, 8)), (Z0, 1)), (-1, 0, 0, 1)),
  "c0-c1<=0": (comb((O1, Fr(1, 3)), (Z0, 1)), (1, -1, 0, 0)),
  "c1-c0<=0": (comb((S0, Fr(1, 3) + Fr(1, 24)), (Z1, Fr(7, 3)), (S1, Fr(1, 8)), (Z0, Fr(1, 3))), (-1, 1, 0, 0)),
}
ok = {}
for k, (got, want) in cert.items():
    ok[k] = tuple(got) == tuple(Fr(x) for x in want)
out["sink_cost_certificate"] = {"inequalities_(c0,c1,d0,d1)": {f"{a}|prev{b}": v for (a, b), v in ineq.items()},
                                "all_equalities_certified": all(ok.values()), "checks": ok}

# ---------------- (O) long-lived Golden orbit ----------------
def fib_blocks(n):
    u = "A"
    while len(u) < n:
        u = ''.join("AB" if ch == "A" else "A" for ch in u)
    return u


U = fib_blocks(6000)
f = []
for ch in U:
    f += [0, 1] if ch == "A" else [0, 1, 1]
s = ''.join(map(str, f))
assert '00' not in s and '11111' not in s
w = strip(theta(f, 801)); W = len(w)
J = (W - 80) // 2
cur = w; maxpos = 0; zeros = 0; checked = 0
for j in range(J + 1):
    assert stream_ok(cur, f[j:j + 13]), j
    assert cur[:60] == theta(f[j:], 60), j
    _, pos = run(cur)
    assert pos is not None
    maxpos = max(maxpos, pos); checked += 1
    if j < J and f[j] == 0:
        zeros += 1
    cur = next2(cur)
out["golden_orbit"] = {"f": "Fibonacci word over blocks A->01, B->011 (no 00, no 11111, aperiodic)",
                       "truncation_width": W, "double_steps_checked": J,
                       "guard13_ok_and_prefix60_equals_Theta(shift^j f)": True,
                       "max_sink_position_on_orbit": maxpos,
                       "positive_defect_steps_(free_zeros)_in_range": zeros}

# ---------------- (X) exhaustive factor check ----------------
q = 40
facs = set(s[i:i + q] for i in range(len(s) - q))
blk = set(U[i:i + 30] for i in range(len(U) - 30))
assert len(blk) == 31   # Sturmian complexity n+1: the block-factor list is complete
worst = 0
for g in facs:
    gg = [int(c) for c in g]
    pre = theta(gg + [0, 0], 2 * q - 2)
    assert pre == theta(gg + [1, 1], 2 * q - 2)   # depends only on g
    _, pos = run(pre)
    assert pos is not None
    worst = max(worst, pos)
out["factor_check"] = {"bit_factor_length_q": q, "distinct_bit_factors_seen": len(facs),
                       "fibonacci_block_factors_len30": len(blk),
                       "Theta_prefix_length": 2 * q - 2,
                       "max_sink_position_over_all_factors": worst}
print(json.dumps(out, indent=1))
