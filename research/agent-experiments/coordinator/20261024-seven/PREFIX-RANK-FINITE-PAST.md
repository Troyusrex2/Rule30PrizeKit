# A checked prefix-rank obstruction and an explicit finite-past model

Four research modules passed the unchanged official checker, with **144
owned declarations replayed through the Lean kernel**. They establish a
specific obstruction to the single-period-five prefix reader, an exact
finite-word bridge to the official dynamics, and a reason to restrict
future searches to rows with an actual finite past. **Problem 1, Q01 and
CQ01 remain open.** The numerical searches below found no proof certificate.

## What the obstruction proves

`Rule30WeightedWordPumpResearch.no_absorbing_tail_decrease` is a general
lemma about signed integer reader costs and integer geometric scale
`lambda >= 1`. Once a reader reaches an absorbing state, strictly lowering
its score by appending a tail would lower it without bound by repeatedly
appending that tail. This contradicts any uniform additive lower bound.
The theorem allows signed costs; a nonnegative-cost assumption is not
being used to manufacture the obstruction.

`Rule30VacuumPrefixRankObstructionResearch` instantiates this lemma with
the correctly aligned 784-state binary prefix reader for the five temporal
phases of the period-five background. The first input symbol is the first
left cell. No center marker is consumed. The complete transition table is
in the Lean source and its absorbing-state facts are kernel checked.

Let `w0` be the first 30 cells of the infinite spatial word `1100001...`,
let `G` be two white-wall Rule 30 updates, and set `w1=G(w0)`, `w2=G(w1)`.
The kernel checks the physical updates and the exact identity

```
w2 = w0 ++ [true, false, true, true].
```

Every word obtained by appending any number of those four-cell tails is
canonical, and has the required alternating even-time head and `01`
odd-time head stream for thirteen double steps. The intermediate word
has the corresponding shifted stream. The reader has already reached
its absorbing state after `w0`.

Consequently `no_single_vacuum_prefix_rank` rules out any choice of signed
integer costs for the two involved phases, arbitrary phase offsets, an
integer geometric scale at least one, and any uniform additive lower
bound, if the score must strictly decrease on the first update and
nonincrease on the second. This refutes that precise rank family on the
forward-only domain. It does not rule out all readers, real geometric
scales, ranks using additional information, or ranks on a smaller domain.

## Why finite past matters

The starting word of that obstruction is not the two-step image of any
finitely supported left row whose head is black. This is also a theorem,
`Rule30FinitePastFrontResearch.obstruction_not_finite_image`, rather than
an inference from failed bounded predecessor enumeration.

The uniform fact behind it is `two_step_front`: if the last black cell is
at depth `m >= 1`, then after two updates the cells at depths `m`, `m+1`,
`m+2` are respectively `false,true,true`. The kit's moving-edge theorem
fixes the new last black depth at `m+2`. The obstruction word ends in
`true,true,true`, so it cannot be such an image.

This distinction prevents an overclaim: the obstruction does not by
itself invalidate a rank required only after an actual finite history.
Every hypothetical infinite finite-support counterexample, after its
first double step, has a real finite predecessor. Merely storing a label
for the previous free bit does not enforce that condition.

`Rule30FiniteLeftWordResearch.row_next` separately proves that the binary
finite-word update equals the official `zrow` at every depth, retaining
both new cells at the expanding front. Its support and prefix-locality
lemmas hold for all lengths and times.

## The revised experiment and its controls

The released `left-finite-past` package streams a canonical finite
predecessor `P`, constructs the entire current row `G(P)`, and constructs
the entire next row `G(G(P))`. The two outputs have delays two and four
and lengths `length(P)+2` and `length(P)+4`. Eight zero inputs flush both
fronts. Current-row scoring stops after its own fourth flush; artificial
zero padding is never charged as part of the finite current word.

A finite-prefix filter enforces the selected future horizon and the
eventual conditional free-word restrictions used by the earlier search.
It also enforces the immediate past free bit associated with the phase
context. This remains a candidate conditional reduction, not a new Lean
proof connecting the whole numerical graph to CQ01.

Independent controls passed:

- 1,024 full-front comparisons with a literal Rule 30 truth-table update.
- 32,768 exhaustive finite-predecessor branch-language comparisons for
  horizons 1 through 4 and input lengths 1 through 11.
- 78 endpoint comparisons for a nontrivial binary reader.
- 156 exact rational energy identities at scales 1, 3/2 and 2.
- Reverse-growth positive and zero-energy negative solver controls. At
  scale 1 the positive graph certificate was rationally checked. At scale
  2 its native positive optimum was found, but the floating-point model
  did not yield an exact certificate under the attempted rationalization.

The last qualification concerns that calibration, not a successful
Rule 30 rank. No positive Rule 30 candidate was found in this batch.

| Reader | Future horizon | Scale | Native numerical outcome |
|---|---:|---:|---|
| One state | 4 | 1 | Optimal defect rate zero |
| Last three bits | 4 | 1 | Optimal defect rate zero |
| Period-five prefix, 784 states | 4 | 1 | Optimal defect rate zero |
| Period-five prefix, 784 states | 13 | 1 | Optimal defect rate zero |
| Period-five prefix, 784 states | 13 | 2 | Solver error, unknown |
| Last three bits | 13 | 2 | Solver error, unknown |

All six process guards completed normally. Peak process-tree RSS was
below 0.15 GiB and minimum system free memory exceeded 43 GiB on G913.
A normal process exit is distinct from a successful solver verdict.
Neither a numerical zero optimum nor a solver error is a kernel proof
of impossibility. The two errors are retained as unknown outcomes.

## Verification and reproduction

| Module | Owned declarations | Headline checks |
|---|---:|---:|
| `Rule30WeightedWordPumpResearch` | 54 | 4 |
| `Rule30FiniteLeftWordResearch` | 30 | 4 |
| `Rule30VacuumPrefixRankObstructionResearch` | 45 | 7 |
| `Rule30FinitePastFrontResearch` | 15 | 3 |

All four reports have verdict `pass`, successful full replay, no new
axioms, and the official statements imported. Standard axioms are listed
per declaration in the raw check output. Counts include generated owned
declarations and are not counts of independent mathematical theorems.

The reference is kit commit
`3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0, with unchanged
`Check.lean` SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The manifest records byte-exact sources, raw build/check logs, numerical
guard records, numerical sources and completed results under `prefix-rank`.

To replay, copy the four new Lean files and the previously released
`Rule30CriticalChargeOneCoreResearch.lean` into the pinned project.
Compile the core first if it is not already built, then the new files in
the table order, using `lake env lean -o .lake/build/lib/lean/NAME.olean
NAME.lean`. Run the unchanged checker on each module with `--claim
partial` and the headline names in its released report, for example:

```powershell
lake env lean --run Check.lean Rule30FinitePastFrontResearch --claim partial --headline Rule30FinitePastFrontResearch.two_step_front --headline Rule30FinitePastFrontResearch.obstruction_not_finite_image
```

The Python package needs NumPy and SciPy. Run
`python left_finite_past_controls.py`, then individual cases, for example
`python left_finite_past_cases.py --reader vacuum --horizon 13 --scale 1`.
The G913 wrapper additionally uses the existing process-tree guard; its
source manifest and all six guard records are preserved. Run reproductions
in a separate directory so the archived result files remain unchanged.

These results are published as a research record. They are not a new
prize submission and establish no solution of an open prize question.
