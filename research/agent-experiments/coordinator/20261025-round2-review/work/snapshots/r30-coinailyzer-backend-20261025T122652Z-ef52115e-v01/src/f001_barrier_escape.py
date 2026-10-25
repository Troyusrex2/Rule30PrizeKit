"""F001: the generic barrier's three conditions are SATISFIED by simple
readers outside its absorption hypothesis, with nonnegative integer costs.

Words (kit convention, w[i] = depth i+1): w0 = first 30 cells of the
period-seven row (1100001)^inf, A = next(next w0), M = next A, Z = next M
(lengths 34, 36, 38): startWord/middleWord/endWord of
Rule30FinitePastPrefixRankObstructionResearch.  The barrier's conditions are
  (1) E1 bounded below on its domain,
  (2) H0 + E0(M) <  H1 + E1(A),
  (3) H1 + E1(Z) <= H0 + E0(M).
With H0 free, (2)+(3) hold for some integer H0 iff E1(Z) < E1(A)
(take H1 = 0, H0 = E1(Z) - E0(M)).  With costs >= 0, (1) holds with B = H1
on EVERY word, so no domain check is needed.

Reader P (prefix-match): states 0..6 = phase in the background, 7 = reject
sink.  Cost 1 on a letter that matches the phase background, else 0.  It is
NOT absorbed anywhere on commonWord = A[:26] (it absorbs only after a
mismatch with the background), so the barrier's hypothesis
run(T,p,commonWord) = s with s absorbing fails.
Reader W_L (definite / sliding-window, synchronizing delay L): cost 1 when
the last L+1 letters (wall-padded) form a factor of the phase background.
Its state after any L letters is those letters: it never absorbs.
Geometric weight lambda^i on position i, as in the barrier.
"""
import json
from zbl import ether, next2

w0 = ether(30); w1 = next2(w0); A = next2(w1); M = next2(A); Z = next2(M)
assert A == w0 + [1, 0, 1, 1] and (len(A), len(M), len(Z)) == (34, 36, 38)
BG1 = ether(400)                 # phase of A and Z: (1100001)^inf
BG0 = next2(ether(420))[:400]    # phase of M: (1011111)^inf
assert all(BG0[i] == BG0[i + 7] for i in range(390)) and BG0[:7] == [1, 0, 1, 1, 1, 1, 1]
common = A[:26]


def prefix_positions(w, bg):
    pos = []
    for i, x in enumerate(w):
        if x != bg[i]:
            break
        pos.append(i)
    return pos


def window_positions(w, bg, L):
    facs = set(tuple(bg[i:i + L + 1]) for i in range(len(bg) - L - 1))
    p = [0] * L + list(w)
    return [i for i in range(len(w)) if tuple(p[i:i + L + 1]) in facs]


def energy(pos, lam):
    return sum(lam ** i for i in pos)


LAMS = [1, 2, 3, 5, 10, 100]
out = {"A": "".join(map(str, A)), "M": "".join(map(str, M)), "Z": "".join(map(str, Z)),
       "commonWord": "".join(map(str, common))}
pA, pM, pZ = prefix_positions(A, BG1), prefix_positions(M, BG0), prefix_positions(Z, BG1)
assert len(prefix_positions(common, BG1)) == 26          # never absorbed on commonWord
out["prefix_reader"] = {
    "matched_lengths_A_M_Z": [len(pA), len(pM), len(pZ)],
    "positions_Z_strict_subset_of_A": set(pZ) < set(pA),
    "conditions_hold_for_every_lambda>=1": set(pZ) < set(pA),
    "witness_lambda1": {"H1": 0, "H0": len(pZ) - len(pM), "E1A": len(pA), "E0M": len(pM), "E1Z": len(pZ)},
    "absorbed_on_commonWord": False}
rows = []
for L in range(2, 16):
    a, m, z = window_positions(A, BG1, L), window_positions(M, BG0, L), window_positions(Z, BG1, L)
    rec = {"L": L, "E_unit_A_M_Z": [len(a), len(m), len(z)],
           "Z_positions_strict_subset_of_A": set(z) < set(a),
           "conditions_hold": {str(l): energy(z, l) < energy(a, l) for l in LAMS}}
    rows.append(rec)
out["window_readers"] = rows
out["summary"] = {
    "prefix_reader_escapes_all_integer_lambda": out["prefix_reader"]["conditions_hold_for_every_lambda>=1"],
    "window_L_escaping_lambda1": [r["L"] for r in rows if r["conditions_hold"]["1"]],
    "window_L_with_Z_subset_A_(all_lambda>=1)": [r["L"] for r in rows if r["Z_positions_strict_subset_of_A"]]}
print(json.dumps(out, indent=1))
