# Both globally finite-support one-step Subset implications fail

Status: exact finite-state closure, independently implemented transition
audit, and literal complete-support counterexamples. This is not a Lean
theorem and does not supply an all-time Common counterexample.

Use the frozen CommonPast definitions, with oldest coordinate the least
significant integer bit. Missing older cells are white. Write D=A xor B.
Common at a row means `D_j H_(j+1) = H_j D_(j+1)` for every natural j;
Subset means `H_j D_j = H_j` for every j. A and B update by literal F,
and H updates by the exact mixed mode from the frozen source, whose SHA256
is17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3.

## Complete-support counterexamples

All initial rows below are zero after their stated support, and the output
includes every newer cell created by the radius-two update.

| Direction refuted | Input (A,B,H) | Output (A',B',H') | Input D | Output D |
|---|---|---|---:|---:|
| forward | (25,2,24) | (111,14,104) | 27 | 97 |
| backward | (33,34,24) | (231,238,8) | 3 | 9 |

The forward input has Subset. Its output fails Subset exactly at j=3.
Input D has support{0,1,3,4} and H has{3,4}; output D has{0,5,6} and H
has{3,5,6}. These supports verify Common at every pair on both rows,
including all tail pairs. The new unsupported mode bit at3 is separated
from nonzero D by zero positions2 and4.

The backward input fails Subset at3 and4; its output satisfies Subset.
Input D has support{0,1}, H has{3,4}; output D has{0,3}, H has{3}.
Again Common holds at every pair in both full half-line rows. Thus neither
direction follows from Common at the input and output, even with genuine
older white boundary and all three initial rows finitely supported.

## Exact graph and completion semantics

Read symbols `s=a+2b+4h` older to newer. A state retains the last two input
symbols, the previous output symbol, and two flags recording whether input
or output Subset has failed. The initial state contains only white symbols
and false flags. Each transition computes the literal next output and
checks the new input and output Common adjacencies. The state bound is
8^3 times4 =2048; the complete reachable graph has364 states and2912
labelled transitions, including rejected edges.

At an input cut, two explicit white symbols compute all remaining possible
nonzero outputs. All later outputs are zero. Common with the next zero is
automatic, so these finite checks imply the predicates globally, without a
right-edge wrap or discarded output cells. Spatial induction proves that
every read path corresponds to the literal input and its one-step output;
conversely every finite-support input follows such a path. This provides
an exact all-width language test, without a width census or time horizon.

The independently implemented auditor checked every transition, reachability
of every node, closure, all completions, and each complete literal witness.
Completed `(Subset input, Subset output)` pairs are all four possibilities:
00,01,10,11. The witnesses found for01 and10 have lengths6 and5 respectively.
No minimality claim is needed.

Root additionally requested the case where only D and H have finite
support, while A and B share an arbitrary infinite background tail.
The same graph was checked with each of the four two-symbol tails from
{000,110} (symbol integers0 and3). After these two equal-background cells,
every later output has D=H=0 regardless of subsequent common background
bits, and its Common adjacency is automatic. All1456 state/completion
combinations were checked; the same four truth pairs occur. The explicit
zero-tail counterexamples already refute both strengthened implications.

## Exact temporal limit of the forward witness

Only this supplied forward witness was followed beyond the one-step test,
as requested. Its global rows are:

| Time | A | B | H | Common globally |
|---|---:|---:|---:|---|
| 0 | 25 | 2 | 24 | true |
| 1 | 111 | 14 | 104 | true |
| 2 | 401 | 50 | 392 | true |
| 3 | 1783 | 222 | 1688 | false |

The first Common failures are pairs(3,4) and(4,5) at time3. The trace stops
there. This rules out an all-time Common interpretation of this witness.
It does not settle initial-Subset preservation under genuine whole-half-line
all-time Common, the finite-white safety conjecture, or a prize target.

## Reproduction and preservation

Run `python -B probe.py`, then `python -B audit.py` in a private owned copy.
The first builds one closed spatial graph; the second checks the certificate
with an independent Boolean/Rule30-lookup implementation and literal complete
supports. Source and evidence hashes are in the frozen manifest. Both guarded
jobs finished below0.3seconds with less than20MiB RSS. No SAT, width sweep,
temporal horizon sweep, or further search followed the failures.
