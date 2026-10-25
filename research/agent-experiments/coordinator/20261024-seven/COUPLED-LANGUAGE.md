# Stronger coupled words, population certificates, and an open counting target

**Problem 1, Q01 and CQ01 remain open.** This record extends the
[even-coordinate investigation](EVEN-SUPPORT.md). All seven original outside
responses were already attempted in [REPORT.md](REPORT.md). No new prize
essay has been submitted from this work.

## Two uniform forbidden words, fully kernel checked

Use the kit's `u R k`, the first cell of the driven right half at time
`2*k+1`, and put `s_R(k)=!u R k`. These are the free bits of `Psi R`.
For **every** right half `R`, including infinite ones, and **every** onset,
`s_R` contains neither `010110` nor `1011010` (time reads left to right).
These are additional constraints beyond the previously verified absence
of `00` and `11111`.

- `Rule30CoupledSixWordResearch.psi_free_no010110` states the six-bit
  result directly for the official `zrow (Psi R)`.
- `Rule30CoupledSevenWordResearch.no_free_1011010` states the seven-bit
  result as a list of complements of the official `u R`.
- `Rule30CoupledWordCertificateResearch.forbidden_of_check` is a reusable
  soundness theorem for finite word certificates, uniform in `R` and onset.
  Its exact-length light-cone proof removes two unnecessary input cells
  from the original six-word check's representation.

The finite calculations enumerate Boolean windows with `decide +kernel`.
The bridge to driven evolution uses the attributed
Villafuerte/Antigravity `drvRow`/`col1_drvRow` block already independently
replayed in the previous release. The new exact-length bridge is proved
here. None of these theorems assumes that a numerical search was exhaustive.

## A population checker with checked state transitions

For a free stream `s`, let

`E_s(d) = recon (alt s) (2*d+2) 0`, and
`e_s(n) = sum_{d<n} E_s(d).toNat`.

`Rule30GoldenBudgetResearch` proves soundness of a complete branching search
with an upper budget on `e_s`, with no assumption about the spacing of its
black coordinates. The depth-first, packed and whole-integer variants have
separate semantic proofs. Small regression checks agree with the original
frontier checker for all three budgets 0,1,2 and horizons 0,...,17; boundary
cases first succeed at 5,12,17 respectively.

The completed budget-four certificate proves

> For every infinite Golden stream `s`, `5 <= e_s(50)`.

Golden means no `00` and no `11111`. The certificate is a DAG of 717 live
states, in six data parts plus a checked root. Every supplied integer state
is connected to its children by Lean's definitional equality for the
official reconstruction step. Every pruned child is checked separately.
The numerical planner is not trusted. All declarations in every part were
replayed by the unchanged official checker.

`Rule30GoldenBudgetCoupledResearch.psi_at_least_five` consequently proves
that `Psi R` has at least five black cells among even depths 2,4,...,100,
for arbitrary `R`. The module also excludes seed-center alternation from
any time whose corresponding left row has at most four such cells.

**Five black cells are not infinitely many.** The generic theorem
`uniform_width_of_all_budget_checks` still needs successful termination
for **every** budget. That hypothesis is not proved.

## What failed, and how memory use was controlled

Numerical complete trees for budgets 8 and 10 become extinct at horizons
102 and 117; these are not Lean certificates. Budget 12 hit its state cap
and is explicitly inconclusive. The initial-state bug in an earlier
prototype was corrected before these runs; the invalid prototype's data
are excluded from this release.

Whole-search, partitioned-list, packed-component and whole-integer probes
for budget 8 exhausted the free-memory guard. No pass is claimed for them.
For example, the whole-integer probe stopped at about 4.942 GiB sampled
process-tree RSS and 1.964 GiB free RAM. The explicit-state budget-four
parts instead stayed below 1.3 GiB sampled process-tree RSS.

All jobs retained the existing limits: 300 seconds, 8 GiB process-tree RSS,
and at least 2 GiB available system RAM. Resource samples are observations,
not exact allocation bounds. No machine configuration was changed.

## An explicit unbounded target, not a solved inequality

Let `z_s(n)` count the zeros among `s(0),...,s(n-1)`. A candidate is

> `z_s(n) <= 3 * e_s(n)` for `s=s_R`, every finite right half `R`, every `n`.

`Rule30CoupledChargeReductionResearch.CQ01_of_charge` proves a more general
reduction for any fixed finite factor `C`: this counting inequality for
every finitely supported `R` would imply CQ01. Its supporting lemma proves
`n <= z_s(5*n)` for every Golden `s`. Thus finite even support would bound
`e_s`, the proposed inequality would bound `z_s`, and the Golden condition
would contradict that bound.

The counting inequality is an **explicit hypothesis**, never an axiom or
an established fact. The reduction itself passes full kernel replay.
It settles only the coupled period-two target if its premise is supplied;
even that would leave the other periods in Prize Problem 1 open.

Evidence for and against particular versions:

- Factor two fails for actual right dynamics. The prefix
  `11110110110` has `E` equal to `0x10`, three free zeros and only one black
  even input. One right initial witness is `0x2de189`; its 12-bit trace is
  `111101101101`. The prefix query correctly reports failure at length 11
  even though the inequality recovers at length 12. Independent exact
  right evolution and left decoding check the witness.
- Factor three fails at length 197 when only the six-word constraint is
  added to Golden. Thus that language strengthening alone is insufficient.
- A width-2048 beam avoiding all forbidden words from the length-14 image
  found no factor-three counterexample through 2048 bits. This is heuristic.
- The complete numerical right-image census through length 30 satisfies
  factor three at **every prefix**. A query with actual right dynamics
  found no counterexample at length **48**. The all-prefix-through-48
  query timed out, as did the length-96 query. Neither timeout is a result
  for or against the inequality. No one of these solver results is a Lean
  theorem or an unbounded proof.

Nonnegative local, multi-step and prefix-parity ranking searches were also
tried with the stronger six- and seven-word guards. No tested fit survived
the held-out checks. The reports preserve infeasible, unknown and failed
fit outcomes separately.

## Exact finite language experiments

Direct bit-parallel enumeration covers every 24-bit right input for
12 free outputs, and every 28-bit right input for 14 outputs. It finds
115 and 188 output words respectively, versus 238 and 560 Golden words.
Every right continuation has one of these finite prefixes by the light cone.
These computations are numerical; their full language claims are not
Lean verified. Only the two new forbidden-word theorems above are.

A separate projected SAT enumeration finds all 668 words of length 20 and
all 3578 words of length 30, terminating with UNSAT after blocking output
words rather than enumerating inputs. Every returned word has a separately
checked exact right-evolution witness. Its shorter-prefix images agree
with the direct exhaustive enumerations; two solver engines also agree on
the complete length-20 image. SAT completeness remains outside Lean.

The finite automaton forbidding all minimal missing words through length
20 permits 5160 words at length 30, while the actual census finds 3578.
So this finite guard is an overapproximation, not an exact description of
the right-boundary language. No polynomial, subexponential or positive
entropy growth law for the true language is proved.

## Independent contribution audit and reproduction

The full source of Jean-Pierre Goux/Claude's
[three-fifths black-run result](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261025-0554f7)
was independently compiled and all 143 declarations replayed locally.
Attribution and the original source hash are in
[external/0554f7-provenance.json](external/0554f7-provenance.json).
This improves a linear run bound; it does not supply a sublinear bound or
prove center nonperiodicity. We do not claim authorship of it.

[language-budget-artifacts.json](language-budget-artifacts.json) records
all exact source/report hashes, declaration counts, headlines and attribution.
The official kit pin is `3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0,
with the unchanged `Check.lean`. Earlier prerequisites are in
[even-support-artifacts.json](even-support-artifacts.json).

After replaying those prerequisites in a reference checkout, run:

```text
python replay_language_budget.py --audit-only
python replay_language_budget.py --project PATH_TO_REFERENCE --lake PATH_TO_LAKE
```

The numerical scripts require NumPy/SciPy and, for solver runs, Z3. This
machine's Z3 5.3.1 is workspace-local under `Rule30/toolchain/python-research`.
All claims and failures remain distinguishable without installing it: the
Lean sources and replay reports are separate from numerical search outputs.

Further agent work should target a proof or counterexample to the explicit
coupled charge inequality, a justified richer language invariant, or a new
unbounded termination argument. Return independently classified results
through the [shared response format](../../RESPONSE_FORMAT.md); keep failed
experiments and avoid replacing an open premise with a finite test.
