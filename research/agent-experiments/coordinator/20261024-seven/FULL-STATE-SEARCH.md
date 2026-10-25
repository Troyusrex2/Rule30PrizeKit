# Complete spatial states, conditional restrictions, and failed rank readers

Problem 1 and the coupled period-two question CQ01 remain open. This release
records searches on **complete finite spatial configurations**, including
both moving ends. It also releases two failed neural readers, their data,
weights, independent tests, and actual-lifetime labels. None is a universal
rank certificate. The independently checked external reduction below is
due to **Emerson Villafuerte; Antigravity (Google DeepMind)**.

[`full-state-artifacts.json`](full-state-artifacts.json) identifies the
126 archived files by their raw SHA256 hashes. Previous reports and manifests
are retained unchanged. The earlier, genuinely new quantitative defect
theorems are in [QUANTITATIVE-DRIFT.md](QUANTITATIVE-DRIFT.md); this release
does not claim another prize result.

## What changed in the search

The earlier ordered readers operated on anti-diagonals in an inverse spatial
reconstruction. Here a word retains an entire actual finite configuration.
In the center-out representation, token zero is `3`, and token `d > 0` is
`left(-d) + 2*right(d)`. The final token is nonzero. Consequently, the word
has a unique finite radius and represents both zero tails exactly.

The exact radius-two transducer accepts center evolution `1 -> 0 -> 1`.
It delays two input tokens and flushes four zero pairs. Its output is two
tokens longer than its input, retaining the newly created fronts. It never
trims the output to the old interval. Independent literal Rule 30 controls
checked 4,096 canonical folded words and 1,024 accepted updates. A separate
outer-to-outer marked-row implementation checked 1,280 words and 304
accepted updates.

Product-graph inequalities cover arbitrary input radius within their stated
domain. They are stronger than merely fitting a finite collection of
trajectories, but their CA, language, and rank bridges are **not formalized
in Lean**. All numerical nonexistence observations below concern the tested
certificate families, with the specified sufficient simulation strategies.

## A verified restriction that earlier searches omitted

[R30-20261025-d1bcba](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261025-d1bcba)
proves `Rule30Submission.Psi_enters_bad_of_finSupp`: if `Psi R` were
finitely supported, the driven right half would eventually remain in the
bad rank class of any applicable certificate. Its width-six instance also
gives eventual exclusions on the free-bit language.

The official public record reports a full replay of 735 declarations.
Our independent replay covers an extracted prefix containing **247
declarations**, including both `Psi_enters_bad_of_finSupp` and
`Psi_free_constraints_width6_of_finSupp`. Every retained proof byte is
unchanged. Extraction removes the unrelated `Rule30PrizeKit` import and
closes the existing section and namespace. The full original-file local
attempt did not pass its resource guard; we do not call that a successful
local replay. See the
[extraction provenance](full-state-search/external/d1bcba/badclass-extract-provenance-v2.json)
and [passing report](full-state-search/external/d1bcba/badclass-evidence-g913-v2/report.json).

The independent check used Lean 4.35.0, kit commit
`3eca23c0a9fa6b153313655e6d51835406c2d06e`, and the unchanged official
checker. On G913, compilation took 11.125 seconds and replay 12.341 seconds;
the larger observed process-tree RSS was 1.785 GiB. This is an audit and
application of another team's result, not a new theorem attributed to us.

For a black center phase, 39 of the 64 width-six right strips have K6 rank
zero. The modified folded graph tests the first six right bits, then forgets
that prefix. Short words use their actual zero tails for the test. Kernel
checked `K6_checkb` makes rank zero closed under either unknown outer bit.
Independent checks covered 4,096 physical words, 624 accepted bad-class
updates, and 1,024 graph-language paths. This condition is **eventual under
the hypothetical finite counterexample**, not a restriction that every
arbitrary initial configuration must satisfy.

A separate temporal-strip experiment uses all nine width-six forbidden
words, complemented for the free bits, together with the previously checked
guards. A 34-state suffix automaton preserves the required history; 5,448
independent extension checks passed. Additive initial slack is allowed.
This conditional search would still need a formal transient-shift bridge
if it produced a useful certificate.

## Completed graph searches

Every ordinary LP below has a homogeneous reward variable in `[0,1]`.
All-zero energies make reward zero feasible. A positive reward must satisfy
every inequality after rational reconstruction before it is a candidate.
The displayed zero optima are native solver results, **not Lean
impossibility proofs**.

| Family | Completed cases | Result |
|---|---:|---|
| Nonnegative additive ranks, complete marked rows | 12 | Optimal reward zero |
| Nonnegative additive ranks, center-out rows | 19 | Optimal reward zero |
| Distinguished root plus every two-state post-center transition table | 256 | Optimal reward zero |
| Signed prefix-maximum ranks, fixed current-prefix matching | 19 | Optimal reward zero |
| Prefix-maximum ranks, matching lags 0, 1, and 2 | 57 | Optimal reward zero |
| Local current/previous-prefix policies on seven reader templates | 1,552 | Optimal reward zero |
| Richer prefix-selection game, integer costs bounded by 8 and potentials by 256 | 6 | UNSAT within those bounds |
| K6 bad-class additive ranks | 19 | Optimal reward zero |
| K6 bad-class prefix-maximum ranks | 19 | Optimal reward zero |
| K6 bad-class nonnegative geometric ranks | 95 | Optimal reward zero |
| Signed geometric energy, certified nonnegative over the accepted language | 84 | 82 zero optima, one timeout, one solver error |
| Separate dual-simplex retry of those two unresolved cases | 2 | Error case resolved to zero; other case timed out at 60 seconds |
| Signed geometric energy with a uniform additive lower bound and zero terminal gauge | 84 | 82 zero optima, two timeouts |
| Temporal-strip energies with the complete eventual forbidden language | 35 | Best `epsilon = 1/2`, insufficient for the `1/5` target |

The fixed-prefix and local-policy simulations are sufficient conditions for
prefix-maximum decrease. Their failure does not rule out every possible
matching strategy. The 1,552 policies completed on four G913 shards with
resource reports; 109,312 independent matched-prefix identities passed.
The richer SMT game can keep reading the input after an output prefix is
selected, or stop earlier using a bound on future output gains. Its UNSAT
results remain bounded synthesis results. Synthetic deletion and identity
controls are explicitly labeled; they are not Rule 30 rank certificates.

The geometric families assign

```
E(w) = sum_i lambda^i * C(state_i, token_i)
       + lambda^length(w) * D(final_state).
```

Unlike additive energies, these can grow exponentially with radius. A
constant decrease is charged in the initial product-graph potential before
the geometric scaling. The nonnegative version tested scales `5/4`, `3/2`,
`2`, `3`, and `4`. Independent exact rational path identities and an actual
reversed radius-growth positive control passed. The positive control uses
the reverse direction; it does not establish decrease in physical forward
time.

The signed versions permit negative local costs and terminal values. A
second graph potential certifies a lower bound on the energy of **every
accepted finite word**, rather than assuming local costs must be positive.
The last version permits one finite additive lower-bound constant. Its
terminal gauge follows
`C'(p,a) = C(p,a) + lambda*D(T(p,a)) - D(p)`, which subtracts the same
`D(start)` from every whole-word energy. Four thousand exact rational
identity checks passed. These model bridges and this geometric gauge are
checked by Python here, not claimed as Lean theorems. The earlier additive
gauge theorem is separately formalized in QUANTITATIVE-DRIFT.md.

Both signed sweeps include joint last-two-pair and last-three-pair readers.
The original unresolved unit-scale last-three-pair case remains unknown
after its 60-second dual-simplex retry. The bounded-below sweep has unknown
last-three-pair cases at scales 1 and 3. No timeout or solver error has been
counted as infeasible.

A separate CNF experiment asks whether a finite row can evolve through a
good alternating interval and return to its entire original folded word,
with new pairs appended. Such a witness would obstruct every
extension-monotone rank on that domain. Across radii 8 through 64 and eight
specified double-step lengths, 55 cases were UNSAT and the radius-48,
eight-double-step case timed out. No witness was found. These 56 bounded
queries are not a universal absence theorem or a proof of well-foundedness.

## Full-state learned readers did not produce a rank

Both networks use a terminal-aware, nonnegative ReLU recurrent energy on
the complete folded words. Checkpoint selection uses training constraints
only. Fresh mathematical right seeds are reserved for the larger validation
and test sets. The inherited data filename `actual-bothzero-ordered.npz`
does **not** mean these are the earlier both-white anti-diagonal words.

| Dataset / objective | Training violations | Larger validation violations | Untouched test violations |
|---|---:|---:|---:|
| Complete-row rank hinge | 2,013 / 2,208 | 991 / 1,024 | 2,018 / 2,048 |
| Actual remaining-lifetime supervision, then hinge plus teacher loss | 2,066 / 2,227 | 999 / 1,027 | 2,025 / 2,052 |

Counts come from a separate CPU double-precision audit with tolerance
`1e-6`; neither run had nonfinite outputs. The training budgets were 165
seconds each on G913. Process-tree RSS stayed below 1.7 GiB, with more than
43 GiB free. The failure is not evidence of an out-of-memory training run.

For supervision, every generated finite trajectory was continued until
actual failure of center alternation. No simulation timeout was relabeled
as termination. Repeated identical full words had consistent observed
remaining lifetimes across 5,382 distinct labeled words. All original
initial cases were retained, with their last good transitions added. The
teacher variant used 45 seconds of normalized lifetime pretraining, then
the rank hinge and a teacher loss on training examples. It did not discover
a useful rank or an interpretable feature that can be asserted as a theorem.

The release includes the generators, two compressed datasets, weights,
training reports, independent audits with failing example indices, and
resource reports under `full-state-search/folded-row-reader` and
`full-state-search/folded-row-teacher`. The mathematical hexadecimal seeds
in these files are experiment inputs, not computer credentials.

## Reproduction and next useful work

The archive preserves the actual source bytes used for the runs. Make a
fresh scratch copy before running scripts, because they write result files.
For the original relative-path layout, place the archived instruments at
`<scratch>/wolfram-local/agent-seven-20261024` and the pinned kit at
`<scratch>/current-reference-3eca-20261024`. `universal_folded_badclass_rank.py`
reads the official K6 table from that kit source. Core numerical instruments
use Python, NumPy, and SciPy; the CNF and game experiments additionally use
python-sat and Z3. The recorded game used Z3 5.3.1. Neural records include the
actual package and device information in their training reports.

Representative entry points are `validate_universal_folded_row_rank.py`,
`validate_lagged_peak.py`, `validate_peak_policy.py`,
`universal_folded_badclass_rank.py --peak`, `folded_geometric_rank.py
--badclass`, `folded_signed_geometric_rank.py`, and
`folded_bounded_geometric_rank.py`. The policy program takes `--models`
indices and checkpoints to its own `results` directory. The external
extraction can be checked with the unchanged official `Check.lean`, using
the two fully qualified headline names given above; its archived remote
driver records the complete source and checker identities.

The most useful next experiments should change the invariant, exploit the
conditional restrictions in a materially different way, or resolve a
specific unknown. Simply increasing the same failed network's training
time is not supported by these results. A new rank must be checked exactly
and connected to the actual Rule 30 evolution in Lean before it can close
CQ01. CQ01 itself would exclude period two; it would still leave the full
nonperiodicity prize question open.
