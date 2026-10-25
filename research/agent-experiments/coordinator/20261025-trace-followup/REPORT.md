# Canonical-trace followup and notebook packaging

**Problem 1, Q01, CQ01 and EdgeObservable remain open. No new unbounded
mathematical theorem is claimed in this phase.** The mathematical work here
is diagnostic; the notebook work prepares the previously checked PR27 proof.
No new prize API submission or submission-ready notebook is claimed.

## New diagnostics

`periodic_tail_trace.py` tests initially left-bounded rows whose right tails
are genuinely infinite and spatially periodic. The represented cone is cut
only beyond the observation horizon, where causality permits it. Among
32,004 parameterized starts, with left-edge depths 1 through 7 and right-tail
periods 1 through 6, no different-edge traces match all 129 observations.
The longest agreement has length 23. There are 152 independent scalar and
doubled-horizon controls. This is not an all-time or all-depth statement.

`unrestricted_right_probe.py` instead leaves all initial right cells inside
the cone unconstrained. It reproduces the known edge-depth (2,1) diagnostic:
eight matching observations are satisfiable; nine are not. For fixed depths
(5,4), 32 matching observations are UNSAT in the solver. This is **not** a
Lean certificate, an unbounded theorem, or the older fixed-width edge-horizon
test. No solver UNSAT is adopted as a proof premise.

The public submission metadata was unchanged at 22:22 UTC: 40 entries and
the same verifier pin. The local append-only inbox has no READY marker newer
than 12:57 UTC. No new external unverified theorem was used.

## Checked starting point and catalog relationship

The existing catalog theorem `Rule30TraceEdge.problem1_of_edgeObservable`
was rebuilt and replayed with the unchanged official checker at
`0090056412733accaa27643d3cbbf982104f2251`: all 14 declarations and three
headlines pass, no new axioms. This audits an **existing conditional bridge**;
it does not prove its open hypothesis.

The earlier [finite XOR rectangle](../20261025-staggered-charges/REPORT.md)
is an explicit all-space/time version of a boundary-shielding phenomenon.
It should be read alongside the existing `Rule30ControlledResponse`,
`Rule30FeedbackErasure`, `Rule30TerminalClock` and `Rule30StripeMeeting`
modules. It is not a new claim of complete trace reconstruction or of a
classification of all four-history rectangles. The catalog already supplies
response rewrites, finite feedback erasure and stripe-trace tools. Likewise,
the three-state Mealy representation and automaton-group viewpoint are
already in the kit; deriving that machine again would not be new progress.

The [updated agent brief](BRIEF.md) isolates the canonical observer target
and the failure cases that a new argument must respect.

## Notebook workflow: corrected and tested, full replay still pending

The old 173-declaration notebook waiter ended at 22:24 UTC with state
`wait_timed_out`. It never launched its validation stages and is terminal.
No replacement long-running waiter was started.

Two small tests exposed and resolved packaging issues before the large proof:

1. The converter restores the caller's example assignments. Its stored
   evaluated outputs must be checked rather than assuming the caller still
   has those variables.
2. In the tested conversion, a JSON-style newline-escaped Lean string was
   checked but did not receive an icon. A literal multiline Wolfram string
   with the same Lean bytes does receive the icon. A separate fresh checker
   also needs LeanLink loaded before its checker expression interns the
   package symbols; otherwise Global symbols shadow the package names.

The three-cell LeanLink canary now passes conversion with `UseCache -> False`
and a **separate fresh plain-kernel replay**, across separate narrative
sections. Its one-declaration kernel replay, icon, source round-trip and
notebook hashes agree. This canary is a tool test, not a prize result.

The actual [seven-cell essay source](work/essay/essay.md) includes an explicit
single-seed center control. Its Lean source is unchanged from the already
checked 207-declaration standalone proof, SHA256
`79e050af6000b66bc0c5a47f74d714e2e36b05ad85ad3783925e2e8f4363473d`.

The [unevaluated notebook preview](work/essay/product-parity-preview-unevaluated.nb)
passes iconization, all seven input-cell checks and a byte-exact source
round-trip. Its proof cells have **not been executed**. This preview must
not be confused with a freshly evaluated submission notebook.

Full build and fresh-replay scripts are prepared. The full build did not
start: available RAM was about 4.89 GB, below the unchanged 10.5-GB launch
threshold. The original 300-second / 8-GiB owned-tree / 2-GiB available-RAM
guards remain in place. A fresh full proof evaluation and human review are
still required before any consent request or API submission.
