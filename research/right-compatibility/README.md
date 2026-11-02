# Right compatibility of candidate Rule 30 traces

Troy Lowry with OpenAI Codex, 2026-11-02.

**Research archive. Problem 1 remains open. No novelty or Wolfram acceptance is claimed.**

This audit separates a driven left-half history from an actual full Rule 30 history.
The local right-side conditions can reject an example even when all its left-side
pin conditions hold. The elementary white-run persistence fact is already used by
the kit's `Rule30FiniteWhiteRuns.black_stays`; this archive makes the scope check explicit.

## Proved results

* `RightOneLayer.compatible_iff`: exact conditions for one right-hand column with
  a free farther-right input, for arbitrary center and left-neighbor traces. Put
  `d(t) = left(t) XOR center(t+1)`. In addition to the usual black-center pins:
  consecutive white center cells require `d(t)=1 => d(t+1)=1`; a white-black-white
  center block requires `d(t)=1 => d(t+2)=0`. An explicit witness proves sufficiency.
  `compatible_iff_free_outer` checks the actual two local update equations.
* `RightOneLayerPeriodTwo.compatible_iff_no00`: for an alternating black-first
  center and its pinned left trace, the known no-`00` condition on the free bits is
  exactly sufficient for this **one-column** relaxation. It does not give a full
  right half or a finite right origin.
* `HiddenPairRightObstruction`: the earlier period-11 hidden pair and the arbitrary
  22-tick block-coded pair each have a branch with no full-space extension. The
  obstruction occurs at times 2..4 and 4..6 respectively. The finite-H truncation
  is likewise a driven-half-line example, not a full-space example. Supporting
  constructions are included unchanged so the statements are independently replayable.
* `PeriodTwoGateExclusion.no_010110`: in **any full Rule 30 history**, thirteen
  alternating center cells starting black exclude the left free-bit word `010110`
  at the six intervening white times. The six-cell right-window invariant is
  certified by `decide`, with arbitrary input beyond the window. Induction proves
  the statement for every start time; no finite-support assumption is used.
* `GateScopeAudit.s_already_excludes`: this last word adds **nothing** to the older
  CP* eight-bit `S` grammar. Its exact set is `{8,9,16,18,33,36,66,72,132,144}` in
  low-time order. After the phase/complement conversion `f(n)=NOT g(n+1)`, an S
  window already excludes the new word. We therefore do not reopen an S-based
  failed argument on the strength of this exclusion.

The free-bit word avoids `00` and `11111`, so it strengthens those two elementary
necessary conditions for a general alternating center. Its appearance in unrelated
spatial block tables is not the same statement. A complete literature/novelty review
has not been performed.

## What remains missing

The old `Rule30TraceEdge.EdgeObservable` and the masked finite-left-edge variant
remain open. The excluded examples still invalidate claims about arbitrary driven
left halves; they do not invalidate a claim whose hypotheses include full right-side
compatibility. Other genuine full-space, infinite-left examples remain relevant.

A useful next target is whether the full right recurrence forces eventual entry into
the stronger gap/S grammar, apart from periodic-output cases. The current kit's
`Rule30GateTrap` supplies a trap and an empty-right entry result; that is not a theorem
that every finite right start enters it. No such universal entry result is proved here.
The follow-up `RightRecurrent.lean` now disproves this implication in the
six-cell relaxation with free outer input. Two closed 19-step paths admit arbitrary
concatenation. Their output is eventually periodic **if and only if** the choice
schedule is eventually periodic (`periodic_iff_schedule`); every block violates S.
Choosing the indicator of powers of two gives a proved all-time counterexample
(`counterexample`). Every single step of the strip and the center equation are
checked (`strip_step`, `center_step`). This does not assert an update equation for
the free outer column, an infinite right extension, or finite right origin.

Thus arbitrary concatenation allows nonperiodicity; the specified nonperiodic
schedule necessitates it. A constant choice is periodic. The singleton's choice
has not been identified. The next proof obligation must use actual right-side
recurrence and finite origin, rather than this six-cell relaxation alone.
See `followup/RESULTS.txt` for the precise scope and reproducible witness.
No wider scan was performed.

## Reproduce

Use Python and Lean 4.35.0 already installed. No dependencies are downloaded.

```text
python replay.py --lean PATH_TO_LEAN_EXE --out NEW_EMPTY_DIRECTORY
```

The script copies the supplied source closure, compiles every module, and invokes
the unchanged official `Check.lean` on the six audit modules. Each owned process
has a 60-second deadline. It rejects new axioms, failed replay, and any claim to
have verified a prize target. All claims are partial; open implications remain open.
The manifest records exact source hashes. Standard Lean axioms only; no `sorry`,
`native_decide`, new axiom, or trusted external computation is used.

Related official sources: [Rule30ZeroBoundary](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundary.lean),
[Rule30Coupled](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30Coupled.lean),
[Rule30FiniteWhiteRuns](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30FiniteWhiteRuns.lean).
