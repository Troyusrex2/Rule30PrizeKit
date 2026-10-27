# Marked defect exclusion and three-coordinate return lifting

Status: author build and unchanged full checker PASS. No public writes were
performed from this phase. Source is frozen at SHA256
`40320f742db353ee238fddd6d909c42cc15a74d4a4ce47ecb705bd98bff87362`.

The final source is `Rule30GatedDepthTwoResearch.lean`. Its exact final replay is
`formal/attempt03`: **70 module constants (including generated constants), 11
headline types**, no new axioms, zero source warnings. The fresh leaf compile
took 0.90 seconds; compile, full replay and type printing took 2.82 seconds.
The owned-process guard recorded 3.05 seconds, peak RSS 782,721,024 bytes,
minimum available system memory 44,613,693,440 bytes, and no guard stop. Limits
remained 300 seconds / 8 GiB owned RSS / 2 GiB available memory.

## Exact result

Coordinates are newest-first. `Actual x` is the literal recurrence

    x_i(t+1) = x_i(t) XOR (x_(i+1)(t) OR x_(i+2)(t)).

The defect is `h_i(t)=x_i(t) XOR x_i(t+P)` and `E(t)` is true exactly at
even times. The marked boundary is the all-time equality

    h_0(t) = E(t) AND h_1(t).                         (D0)

`depth_two_impossible` excludes D0 when P is positive and even, the third
newest trace x2 has unit P-defect, and x3 is P-periodic. It assumes `Actual`
for the complete profile family. Its proof uses only recurrences 0 through5,
so the paper's eight-profile local formulation is valid as a proof reading;
that restricted-recursion interface is not the exact exported theorem type.
No whole-orbit clock or period of x0 or x1 is assumed.

`unit_birth_not_near` says an oldest unit P-defect under D0 cannot occur at
index0,1,2. The older coordinates' P-periods are literal hypotheses here.

The bridge does not assume such a unit defect. `tail_period_from_return`
uses actual autonomy to turn an initial returning tail into all-time periods.
`oldest_failure_unit` derives the all-time unit defect at the oldest initially
failing coordinate. `staggered_tail_return` consequently proves that if the
tail from index3 returns at P and D0 holds, every coordinate returns at P.

`state_staggered_return` applies this result directly to the official
`Rule30ControlledResponse.iterate`. `word_staggered_three_return` specializes
to the official `word ([a,b,c] ++ u)`: the arbitrary older finite word u
returns at positive even P, and the extended word's actual orbit satisfies
D0 at every time; then the entire extended word returns at P. The list is
newest-first, its default continuation is literally white, and u may be
empty. No clock of the extended word, supplied child clock, supplied unit
birth, finite observation window, or full-gate premise occurs in this type.
The printed authoritative types are in `formal/attempt03/types.log`.

## Why the local proof works

An exact Boolean change of variables gives an auxiliary q with
q(t+1)=q(t) XOR f(t), where f=x3. The marked recurrence forces g*q=0
and propagation of q=1 at an odd time. Such an odd occurrence would force
q=1 forever afterward, hence an eventually zero drive for anti-P trace x2,
which is impossible. Thus q vanishes at every odd time.

The actual shared predecessor recurrences then force the temporary equality
g=k at all times at least1. This equality is derived; no twin classification
is imported. An even q=1 at a time at least2 propagates forward. Either that
event occurs, or q remains zero from time2. In both cases the drive of x2 is
eventually constant. A constant Boolean XOR drive returns after every even
number of steps, contradicting the actual anti-P identity. The proof never
transports an eventual statement backward to time0 and never assumes a
period of q. All finite Boolean case splits prove local symbolic identities;
there is no clock census or finite-state path certificate in the new proof.

## Prior work and scope

The already verified `Rule30TwoPlateauClockResearch` theorem
`actual_even_two_plateau_or_clock_rigidity` proves a different OR-observer
exclusion across two cells, also without an output clock. In particular,
the full-gated three-cell return consequence is already implied by prior
work and is not claimed as a new result here. D0 by itself does not generally
make the newest OR P-periodic: its OR defect is
h1*(1+x0+E*x1), which becomes h1*(1+x0) at odd times, in Boolean-ring
notation. This phase formalizes the different
marked-defect observer and its direct finite-word bridge, not a blanket
strict generalization of the prior OR theorem.

The mathematical argument comes from the prize_bridge worker's frozen
DEPTH-TWO-EXCLUSION and LOCAL-EXCLUSION-SCOPE notes, independently checked
by root before formalization. Their exact bytes and hashes are retained
under `papers/` and in `sources.json`. The prior OR theorem is recorded there
for comparison, not imported by this Lean module.

This does not prove transfer through arbitrarily many newer coordinates,
an arbitrary-width observer theorem, a physical-center bridge, or any prize
problem. The crucial marked all-time relation D0 remains a hypothesis.

## Validation and reproducibility

The only direct import is official `Rule30ControlledResponse`; its recursive
closure contains eight official modules. `inputs.json` records exact source
and object hashes. `formal/attempt03/dependency-objects.json` records every
copied artifact and its origin. The new leaf was freshly compiled; the eight
official modules were reused from previously built, hash-verified objects.
This was not a cold build of the whole dependency closure.

The read-only reference compiled pin is
`5473ffd075f63c9d626e63b8455805d4831b39ca`; this exact official closure is
unchanged at compatible current pin
`7d665044b904117af9e82328aeb90a30692b2b85`. The unchanged Check.lean hash is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
Lean4.35 executable hash is
`ec7a472d1c12a09b0c0c718f7427c2be527b3f5f07810fdbe076c2507c7a91ea`.
The final compiled leaf hash is
`07c021f813fed79b2c8478496191ef9f9a7528e13426e893d258d3437121ed7d`.

For an independent replay, use a new owned phase with the exact source,
`inputs.json`, `guard.py`, and `replay.py`, preserving their hashes and the
documented reference/object paths. Invoke the guard on the remote machine:

    python guard.py replay.py independent01

The runner verifies reference/checker/toolchain/dependency hashes, builds
the leaf, invokes the unchanged checker on every module constant with all11
headlines, prints their complete types, and rechecks dependency hashes.
The original runner `run.py` additionally performs scoped SSH upload and
downloads evidence. Do not rerun into an existing attempt directory or alter
this sealed phase. No reference tree writes are required.

Attempt01 preserves the original whole2P-clock proof draft and its failed
elaboration: broad simp_all recursively expanded recurrence hypotheses,
with additional Boolean/index normalization errors. Its guard terminated
normally. Attempt02 preserves the successful stronger forward-time core
(53 constants / 6 heads). Attempt03 adds the official semantic bridge and
removes unused clock-wrap helpers. All attempts and guard receipts remain.

No sorry, axiom declaration, native decision, altered checker, or extra
assumption was used to obtain the final result. Root/another agent's later
independent replay or source review is separate evidence and is not claimed
by this author report.
