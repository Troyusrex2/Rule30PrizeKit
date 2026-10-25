# More RAM, bounded certificates, and a weaker unbounded target

The full prize problem and `CQ01` remain open. This continuation separates
an engineering result, a bounded proof, and an unproved counting target.
Nothing here has been newly submitted to Wolfram or awarded a prize.

## The memory failure was real

The unchanged `Rule30GoldenCompactLeafProbeResearch` source checks one
2,453-node subtree. On the original host its guarded run stopped with about
1.96 GiB system memory free. On the 64 GB worker, compilation passed in
93.246 seconds, peaking at 15.923 GiB process-tree RSS. An initial full replay
hit its explicit 16 GiB guard; that run was not a pass. A retry with a 24 GiB
process limit and at least 16 GiB system memory free passed the unchanged
official checker in 88.584 seconds, peaking at 16.379 GiB and leaving at least
29.456 GiB free. Two owned declarations were replayed.

The larger limit applies specifically to this probe on the larger host.
The proof, Lean version, official statements, checker and security controls
were unchanged. Lean used CPU and system RAM; the additional GPU was not
needed. No user configuration or authentication files were copied.

The new prefix-congruence helper (`Rule30GoldenCompactPathResearch`) also
passed full kernel replay: 13 declarations. It proves arbitrary-length
path congruence and zero/one extension equations.

## Budget-eight assembly

The complete budget-eight search has 108,998 live tree nodes. It is split
into 404 closed subtrees with at most 600 live nodes each. Each source
contains a literal state, a kernel-checked `path_eq`, a closed
`decide +kernel` decision, and a theorem about the intended prefix. Numerical
planning is not a premise of the proof.

Three jobs run concurrently, each limited to 300 seconds and 8 GiB RSS,
with a 16 GiB system-free guard. Every successful leaf is independently
replayed by the unchanged official `Check.lean`. Resume requires matching
source, kit, checker and object hashes.

A prototype join used `change` to compare an integer prefix against an
equivalent `or`/power expression. Lean unfolded the long path during that
comparison. A small prototype first exhausted its heartbeat budget; a retry
hit its 4 GiB process-memory guard after 272.012 seconds. The corrected join proves the integer equality
separately, rewrites the general extension equation, and uses it to join the
child proofs. The two-child test passed, and a larger preflight joining 125
leaves replayed 757 declarations in 13.956 seconds, peaking at 0.881 GiB.
The live leaf sources and original manifest were not modified.

All **404 leaves and the corrected root passed full kernel replay**. The root replay checked 2398 owned declarations in 28.195 seconds, peaking at 0.887 GiB RSS. `minimum_nine` proves at least nine black even-code samples among the first 102 for every Golden stream. The separately checked coupled bridge gives at least nine black cells of `Psi(R)` at depths 2,4,...,204, for arbitrary right halves, including infinite ones.

This is a finite population bound, not a proof at all depths. It is useful
for validating the partitioned proof architecture. We are not preparing a
new prize submission merely for this larger finite instance.

## A weaker unbounded target using all spatial coordinates

The previous target charged zeros in the free stream against only black
even spatial coordinates. Finite support of the actual sideways row requires
both odd and even coordinates eventually to be white. It is therefore useful
to count both parities.

Let `z(s,n)` count zeros among `s(0),...,s(n-1)`, and let `b(L,K)` count black
cells at depths `0,...,K-1`. The new constant-one candidate is

```text
no adjacent zeros in s  ==>  z(s,n) <= b(Theta(s), 2*n+1), for every n.
```

The initial coordinate at depth zero is white, so the right side counts the
first `2*n` positive spatial coordinates, including both parities. This
candidate uses no restriction on five consecutive ones and no finite
right-trace approximation. **The displayed inequality is unproved.**

`Rule30TotalSpatialChargeReductionResearch` formally proves that this
candidate implies `CQ01`. More generally it suffices to bound `z(free(R),n)`
by `B + C*b(Psi(R),2*n+1)`, where the natural constants `B,C` may depend on
the finite right half `R`. Full kernel replay passed for 23 declarations and
five headlines. The counting premise is an explicit hypothesis throughout.
Even resolving `CQ01` would only exclude eventual period two; the full
prize problem requires more.

Falsification results for the new candidate:

- A width-1024 heuristic beam reached length 4096 without a counterexample:
  1576 free zeros and 1695 black spatial cells. Direct physical evolution
  rechecked all 8192 boundary cells. This is not exhaustive.
- Independent Boolean CNF found no violating prefix of length at most 48
  in 12.531 seconds, using only the no-adjacent-zero condition. This finite
  UNSAT result is not Lean verified. Length 96 timed out after 90.282 seconds.
- Without the no-adjacent-zero condition the candidate is false; the
  six-bit free word `0x12` is a positive counterexample control.
- The simple local charging rule is already false for the actual empty
  right half: free zeros at indices 81 and 83 have no new black spatial
  coordinate in between. A global argument needs accumulated credit.

A stronger optional version replaces `z(s,n)` by the number of starts of
zero runs and allows arbitrary free words, without a no-adjacent-zero
premise. It survived all 65,536 length-16 words and 96 random longer words
through length 1024. These are finite tests only.
`Rule30ZeroRunSpatialChargeReductionResearch` proves that this stronger
inequality would imply the no-adjacent-zero target and hence `CQ01`; its
15 declarations and three headlines passed full kernel replay. The stronger
inequality itself remains unproved.

## What the new reader and rank tests ruled out

These tests use actual right-driven traces, with independently separated
training and longer held-out depths. None produced a universal rank.

- Nonnegative phase-conditioned letter counts and free-group reduction
  lengths did not yield a candidate. Solver `unknown` and timeouts are kept
  separate from `infeasible`.
- Adding DFA terminal-state features did not rescue the sampled readers:
  48 even-zero readers produced 32 infeasible and 16 unknown results. On
  both-spatial-zero transitions, 48 readers produced 35 infeasible and
  13 unknown results.
- A reader remembering the last three letters fitted 2030 training
  transitions but failed 234 of 693 held-out transitions. Refinement with
  the old failures and longer traces fitted 4808 transitions but failed
  159 of 691 new held-out transitions. We did not promote the training fit
  to a mathematical claim.
- Directed Dyck reductions tested nonlocal, order-sensitive cancellation.
  The initial LP was unknown; an interior-point retry without presolve was
  infeasible. This is a result for that feature family, not all stack ranks.
- Positive semidefinite quadratic energies fitted the shorter both-zero
  data but failed 282 and 437 of 703 longer held-out transitions. The second
  fit also had numerical feasibility errors. Homogeneous variants were
  numerically infeasible. No matrix was accepted as a candidate.

A separate attempt sought a **spatial** telescoping inequality across the
finite inverse-computation triangle. Signed temporal-window costs need not
be nonnegative at intermediate columns, so this differs from the earlier
time-descending ranks. The initial four-letter, window-four fit failed on
1318 longer words. Enforcing a necessary adjacent-column invariant made all
four tested window sizes infeasible. A version storing three adjacent
columns fitted the shorter window-four data but failed on 3107 longer words.
Truth-table and invariant controls passed for 8 Boolean neighborhoods,
484 pair words, 2728 triple words and 126 initial boundary words. These
proxy-language LP failures are not formal obstructions to all spatial
telescoping arguments or to actual Rule 30 histories.

There is now a stronger diagnosis for the simplest count model than a
floating-point solver status. Five actual transitions, in the two contexts
21 and 42, admit integer multipliers `17,39,16,26,12`. Their combined feature
change is componentwise nonnegative while requiring a decrease of 55.
An independent truth-table implementation reproduced the right evolution,
scalar left reconstruction and physical left re-evolution of all five cases.
`Rule30BothZeroCountRankObstructionResearch` kernel-checks the resulting
algebraic contradiction for natural count weights (four declarations).
The exact integer certificate also gives the elementary weighted-sum
contradiction for nonnegative real weights. The Python-to-official-evolution
equivalence of these concrete examples has not been formalized in Lean.
This obstruction excludes only the stated affine letter-count family.

## Provenance and next work

All Lean checks use Lean 4.35.0, kit commit
`3eca23c0a9fa6b153313655e6d51835406c2d06e`, and unchanged checker SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The accompanying manifest binds sources, complete checker reports and
experimental data. Earlier published manifests and failed memory records
remain unchanged.

The public contribution list was refreshed at 2026-10-25 04:10:52 UTC:
38 entries, byte-for-structure identical entries to the previous
03:09:25 UTC snapshot, and the same reference kit. No new contribution
was available to incorporate.

The main mathematical task is a uniform proof or a counterexample to the
new spatial counting target, or a different argument establishing infinite
support. Increasing finite bounds alone will not supply that argument.
