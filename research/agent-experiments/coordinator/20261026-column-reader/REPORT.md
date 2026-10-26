# A learned temporal-column reader with unbounded soundness

Problem 1, CollisionClock, unconditional subset preservation and the
fixed-center past extension remain **open**. This archive proves one new
guarantee: every prefix accepted by the included 17-state reader has equal
temporal columns for all future times, at arbitrary prefix length. It does
**not** prove the converse for rejected prefixes.

This is a local full kernel replay, not Wolfram backend verification, human
review, kit adoption or a prize award. No new prize essay was submitted.

## The object and theorem

Read paired initial bits from the white right boundary toward the left,
in increasing right-edge depth. The alphabet is 00, 01, 10, 11. Each history
evolves by the exact triangular Rule 30 update
`x[j] XOR (x[j-1] OR x[j-2])`, taking negative depths as white. These
coordinates follow a right-moving physical ray; a fixed depth is **not** the
fixed vertical center of the prize question.

`Rule30ColumnReaderResearch.reader_sound` says that for any two actual
right-bounded histories a,b and n>0, acceptance of their length-n initial
prefix implies `a t (n-1) = b t (n-1)` for every natural t. No finite-time
cutoff or temporal-clock assumption appears in this statement.

The proof uses a 47-state coupled certificate. Kernel-checked closure proves
that reader acceptance is unchanged by the exact one-time Rule 30 update,
and that acceptance implies equality of the last input bits. List and row
lemmas bridge the finite certificate to `Actual` and `march` from the earlier
CommonPast module. Induction on time then proves soundness. The certificate
was generated in Python, but its closure, invariant and bridge are checked
in Lean using ordinary kernel reduction. The learner is not trusted.

The acceptance invariant works in both directions under a time step. This
still does not establish that the reader accepts *every* equal column:
that would require proving every rejection eventually exposes a difference.
In particular, state 15's predicted permanent separation remains unproved.

## Learning and independent controls

The L* pilot asks exact membership queries using the full power-of-two
temporal period bound for each finite prefix, rather than a detected tail.
It passed 1,364 scalar controls and reached 17 states after candidates with
2,4,7,11,13,15 states. It used 93,113 membership queries. The final candidate
matched all 87,381 paired words of lengths 0..8 and 6,000 held-out words of
lengths 9..16: 93,381 tests, including 4,411 positives. The stop reason is
`bounded_candidate`; no regularity or completeness claim follows from this.
The JSON's `last_counterexample` concerns the preceding hypothesis, not the
final reader.

An independent truth-table audit recomputes the 47-state product, checks all
5,461 paired words of lengths 0..6 against scalar temporal profiles, and
rejects deliberate wrong-initial-state and missing-state corruptions. It
passed. These Python controls are not themselves Lean verified.

Exact fixed-clock product graphs close at temporal clocks 2,4,8,16, with
64,144,1,296,4,624 states respectively. No classification mismatch appears.
Each closed graph covers arbitrary spatial length **within that clock
class**. These graph checks are Python evidence, not an all-clock proof.

A separate individual-column graph closes at clocks 2,4,8,16,32. In those
graphs, every OR collision with different adjacent columns has constant-one
OR. At clock 64 the graph stops at its internal node cap: 150,002 discovered
states, 147,978 processed. It is not closed; no universal clock-64 conclusion
is claimed. Reachable period-eight profiles with three or five black bits
also falsify a tempting balanced-profile shortcut.

## Proof attempts that did not close completeness

A simple separation invariant fails under local admissibility at clock four;
the included counterexample need not be reachable from the white boundary.
Additive state and edge ranking templates are UNSAT. Additive macro-step
templates for 2,3,4 updates are UNSAT; the six-update search reaches its 50,000
node cap (50,004 discovered), which is an incomplete search, not UNSAT.
Lexicographic digit rankings in both spatial directions for 1,2,3 updates are
also UNSAT in the stated finite templates. These are Z3 diagnostics, not
kernel proofs that every ranking argument is impossible.

Exact profile enumeration through initial width 16 needs up to 45 initial
time bits to distinguish distinct columns. Thus a uniform tiny time horizon
cannot be assumed. No general delay bound was proved. The remaining target
is a proof of completeness or a genuine counterexample, then a derivation
of the preceding archive's CollisionClock statement. Even that would leave
the separate fixed-center past condition needed by the prize strategy.

## Reproduction and scope

The new 211-line module has SHA-256
`ad1d09b6d460b1849017fcf7c99151ad0304ceee8dfc80e78f43bfc1a917da3b`.
The unchanged official checker replays all 119 module declarations and
accepts three headlines with no new axioms. The count includes generated
declarations, not 119 independent new theorems. The included CommonPast
dependency is byte-identical to its earlier 100-declaration full replay;
that is reused work. Pin: `0090056412733accaa27643d3cbbf982104f2251`,
Lean 4.35.0; checker SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

Build plus replay took 2.511 seconds on G913, peak owned RSS 911,200,256
bytes, minimum system free 46,315,163,648 bytes. The 300-second / 8-GiB
owned-tree / 2-GiB free guards were unchanged. Earlier failed development
attempts are not counted as passing runs. Final logs and reports are included.

Run `python verify_artifacts.py` to audit exact bytes and recorded scope.
To replay Lean, prepare the pinned kit, place both `work/*.lean` modules in
its project root, compile CommonPast then ColumnReader and use
the unchanged checker. From the project root:

```text
lake env lean -o .lake/build/lib/lean/Rule30CommonPastResearch.olean Rule30CommonPastResearch.lean
lake env lean -o .lake/build/lib/lean/Rule30ColumnReaderResearch.olean Rule30ColumnReaderResearch.lean
lake env lean --run Check.lean Rule30ColumnReaderResearch --claim partial --headline Rule30ColumnReaderResearch.acceptance_invariant --headline Rule30ColumnReaderResearch.prefix_step --headline Rule30ColumnReaderResearch.reader_sound
```

The Python scripts run beside their input JSON. Most use the standard
library; `guard.py` needs psutil and the ranking scripts need z3-solver.
`check_formal.py` records the actual isolated Windows paths used; adjust
paths to reproduce elsewhere without changing the official checker.
The public refresh at 03:01:38 UTC found the same pin, 40 entries and
unchanged skill 1.17.3. No unchecked external theorem was adopted, and no
historical-priority claim is made.
