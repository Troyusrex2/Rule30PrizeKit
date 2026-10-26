# Finite white-boundary Common windows do not preserve subset

**The all-time Common preservation conjecture and Prize Problem 1 remain
open.** This checkpoint proves a failure of a proposed short-window route,
using the genuine white boundary and finite initial rows. It complements
the preceding spatial-cycle diagnostic, which deliberately lacked that
boundary. There is no new prize submission or Wolfram verification claim.

## The kernel-checked finite-white example

Credit for the smaller forward witness: the Codex Cedar team for Troy Lowry.
The root agent independently recovered it with a different two-step
transducer, checked its complete support, and wrote the Lean proof.
Integers encode rows with the oldest position in bit zero:

| Time | A | B | H | Common on the whole half-line |
|---|---:|---:|---:|---|
|0|25|2|24|yes|
|1|111|14|104|yes|
|2|401|50|392|yes|
|3|1783|222|1688|no|

The two actual backgrounds and their mixed linear mode evolve by the exact
`march` and `modeStep` definitions from `Rule30CommonPastResearch`. The Lean
definitions are recursive histories for EVERY natural time. Only their
first four rows are identified with the table. The proof therefore supplies
`Actual A`, `Actual B`, and `Mode A B H` without a temporal cutoff or a
spatial wrap. All three initial rows have finite support.

At time zero, H is supported in A XOR B. At time one, depth 3 is black in H
and white in A XOR B, so subset has failed. Common still holds at every
adjacent pair at times 0, 1 and 2, including beyond the new rightmost cells.
At time 3, Common fails at the pair starting at depth 3. The exact scalar
audit also finds the pair starting at depth 4; the headline needs only one.

`Rule30FiniteCommonWindowResearch.finite_common_window_does_not_preserve_subset`
states all those hypotheses and limitations together. Finite kernel checks
cover the relevant sites; separate support lemmas prove the white tail for
every remaining natural index. Induction identifies the literal rows with
the full recursive histories. No numerical horizon is extrapolated.

The unchanged official checker at pin5473ffd075f63c9d626e63b8455805d4831b39ca
fully replayed all56 new constants and both headlines. The100-constant
CommonPast dependency was freshly rebuilt and fully replayed, and its bytes
match the previous publication. The new module took1.74s at742MiB peak owned
RSS. The original attempt needed the two imported predicate definitions
unfolded before the kernel decision tactic could synthesize their decidable
instances; its failed source and log are retained. This is a local full
kernel check, not a new backend or human-review verdict.

## What the finite-state controls rule out

Cedar's exact one-step transducer scans initial triples and keeps the two
older input triples, the previous output, and the two bad-subset flags.
Its complete graph has364 reachable states and2912 labelled transitions.
An independent implementation checked every edge, reachability, closure,
all completions and the complete literal witnesses. Two white closing cells
include every potentially nonzero output; later outputs are zero. Allowing
either equal-background symbol at each closing cell gives the same result.
Both directions of one-step subset propagation fail:

| Direction | Input (A,B,H) | Full output (A,B,H) |
|---|---|---|
| subset true to false | (25,2,24) | (111,14,104) |
| subset false to true | (33,34,24) | (231,238,8) |

Both complete input and output rows satisfy Common. The backward witness
and the complete graph are independently audited computational evidence;
only the forward three-row witness is promoted to a Lean theorem here.
The root's separate manually derived forward example (4,108,8) produces
(28,404,40); Cedar's audit checks it as well.

The earlier truncated width-four recurrent example has a different scope:
A cycles through[1,7,9,15], B through[2,14,2,14], with H=8. Internal Common
holds throughout, while subset changes. Its omitted newer constraints fail
after zero-extension. It refutes an argument based only on recurrence of
truncated prefixes, not the actual whole-half-line statement.

The root's independent temporal-depth-two scanner found the same forward
witness after2308 discovered states and4176 examined edges. It stopped at
that witness; those figures are not a complete graph certificate. The
literal audit checks the whole rows and the first Common failure. We did
not keep increasing temporal windows after this route failed.

## Remaining work

All-time Common is essential to the open preservation target. Neither
one-step invertibility nor a three-row Common window replaces it. These
counterexamples do not contradict the earlier conditional collision-clock,
front-stability, past-lift or two-plateau theorems. They do not prove safety
completeness, observer completeness or a physical-center bridge. The next
argument must exploit unbounded temporal information with the genuine
boundary, rather than assume a local preservation rule that is false.
