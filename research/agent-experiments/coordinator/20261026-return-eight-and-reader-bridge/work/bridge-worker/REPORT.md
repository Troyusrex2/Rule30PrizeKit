# Safety completeness and the remaining two-history shielding problem

No implication from global safety completeness to full sink separation,
ObserverCriterion, or Prize Problem 1 was proved. One genuine part of that
bridge is now kernel-verified: **assuming global Safe -> whole-word return
after eight steps, an equal-output pair with a Safe common output cannot be
in reader state15, at any spatial width.** A precise immediate-parent
shielding statement remains open. Its boundary-free version is false, even
with an arbitrarily long older ancestry made entirely of unsafe profiles.

All work in this directory is private research. No publication, submission,
main-repository edit, shared-reference edit, or Cedar-file edit was made.

## Verified conditional bridge

`PrizeSafetyBridge.ReturnComplete` is exactly

    forall xs, Safe xs -> evolution 8 xs = xs.

Here xs is the entire finite older-first word, both older boundary cells are
white, and Safe means that its newest temporal trace never contains00.
The theorem does not replace whole-word return by newest-bit return.

`safe_equal_reader` says: for every paired finite word ss, if its A-word is
Safe and both words have equal newest bits at every time, then the existing
17-state reader accepts ss. Equality transfers safety to the B-word.
`safe_sink_separates` is the contrapositive for initial reader state15.
Neither theorem asserts ReturnComplete.

The nontrivial finite component is `safe_language_equal_reader`. For two
words accepted by the 13-state safety language, equality of their first nine
newest observations implies acceptance by the paired 17-state reader. The
28 safety-certificate states on each side give an exact784-state product.
There are1024 live paired transitions and27 equal-profile accepting states;
none is reader-rejected. The absorbing safety state11 permits rejecting
branches to be discarded without a word-length bound. A spatial induction
in `accepted_profiles` then covers every paired word length. The finite data
are checked by ordinary kernel reduction; Python is not trusted by Lean.

Frozen source SHA256:

    dfe6ac2e1010a8e04d2b8bcae4f71501950cfb4a2de83e56bbfc604f7a009b17

The unchanged official checker replays all100 declarations in the new
module and passes all three headlines. This count includes definitions,
table machinery, generated declarations, and finite certificate facts.
Five imported research modules were freshly built and fully replayed in
the owned G913 folder: CommonPast100, ColumnReader119, SafetySoundness137,
SafetySemantics75, SafetyBridge8. These439 dependency declarations are not
new work. Official imports came from the existing verified pin5473 project.

Pin:5473ffd075f63c9d626e63b8455805d4831b39ca.
Checker SHA256:b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905.
The successful leaf run took3.70s under the unchanged300s/8GiB-owned/
2GiB-free guard, sampled peak797,999,104 bytes. Initial namespace/core-tactic
and elaboration failures are preserved under attempts; none is counted as
a pass. The coordinator independently replayed the frozen source as well.

`audit.py` independently uses the literal eight-entry Rule30 truth table to
validate all784 short product witnesses,73,350 cell updates, and the reset
control's16 rows. This is additional computational validation, not another
kernel theorem.

## The exact remaining shielding statement

For a finite word w write Tr(w)(t)=newest(evolution t w). The useful open
statement has no canonicality restriction and compares traces, not raw words:

    length u = length v,
    Tr(u ++ [a]) = Tr(v ++ [b]),
    Tr(u) != Tr(v)
      ==> Safe(u ++ [a]).

Call this immediate-parent shielding. It asks whether a genuine coalescence
of different parent traces can produce anything other than a Safe common
child trace. Known reader-accepted coalescences have an alternating child,
but that observation is not a proof for reader state15.

There is a concrete paper reduction from this statement plus ReturnComplete
to reader completeness. Induct on equal word length. If the two parent
traces agree, apply the induction hypothesis to the parents and then the
existing `extension_words`/`same_snoc` three-time extension theorem to the
common child trace. If the parent traces differ, immediate-parent shielding
supplies Safe, and the newly proved `safe_equal_reader` supplies acceptance.
The base case is the reader's accepting empty word. This reduction has not
been separately formalized here, and the shielding premise remains unproved.
It would activate the prior reader-to-CollisionClock and finite-initial
subset-preservation theorems. The fixed physical-center observer remains a
separate issue even after those results.

This is not a claim that renaming shielding solves the problem. It identifies
the exact part not supplied by the verified safety-language product.

## What the00 reset does and does not give

If an equal common child trace has00 at timeT, the Rule30 equation forces
both immediately older cells to be zero at timeT, on both sides. Thus both
words have newest suffix000. More generally a temporal zero run of lengthL
forces a spatial zero cone of width2L-1 at its beginning, until the boundary
is reached. This is a paper local deduction, not a new formal headline here.

Under ReturnComplete, any all-time equal sink pair must have an unsafe
common output, by the new theorem. The existing sink time-invariance theorem
therefore moves a hypothetical counterexample to a time with shared000
suffix. It can also be normalized modulo the existing sound reader
equivalence. However, time evolution preserves canonicality and the first
black position of a nonzero finite white word. Repeated resets alone do not
strictly decrease canonical effective width. Deleting the reset suffix
requires a new argument that recovers the shorter parent trace from the
whole observation history.

One complete excursion does not suffice for that decoder. The actual finite
white canonical words

    A = 100001000000
    B = 100001100000

have paired reader state15. Their newest bits at times0..7 both read
`00010100`: the first nonwhite excursion leaves at time3 and returns to a
three-white suffix at time6. Their parent traces over the same times are
`00010100` and `00101100`, differing already at time2, inside the excursion.
Their full newest traces subsequently separate. This control refutes only
the proposed ONE-excursion parent decoder, not infinite return coding,
immediate-parent shielding, sink separation, or P1.

`ResetExcursionControl.one_excursion_counterexample` encodes these exact
finite facts with ordinary kernel reduction. Frozen source SHA256:

    e9cf39dc7e58b1b76971e6d0685756d323998e549d2fc57b7fadb76820e4bb1b

The coordinator's independent full replay passed all6 declarations in1.53s;
its hash-matched report and unchanged guard receipt are retained under
independent-root-review. This worker did not schedule a duplicate replay.
`first_return_control.py` stopped after13
targeted candidates in the fixed family1(00|11){0,1}^6 000. It is not a
temporal-clock/width census or an all-time equality test.

For comparison, the permitted accepted aliases101·0^9 and011·0^9 have equal
unsafe traces of least period64 and repeated shared000 resets. Their parent
traces also agree. They are a control against literal prefix uniqueness,
not a counterexample to the parent-shielding target or reader completeness.

## All-time local controls and the boundary that cannot be dropped

The prior four-column plateau collision already defeats immediate-parent
shielding with free older inputs. Its common adjacent OR is01111111.
Appending a child initialized at0 gives the common period16 trace
`0010101011010101`, which is unsafe, although the parent profiles
01010111 and00110101 differ. The local equations hold cyclically for all
times. Its two oldest profiles remain free.

There is a useful restriction on that old control: its B-side has an
alternating k=01010101 immediately newer than l=11001100. Under
ReturnComplete the safety DFA/profile certificate excludes this pair:
the possible nine-bit predecessor profiles for an accepted alternating
column are170,341,511, whereas this l has profile307. This is a conditional
ancestry exclusion, not a proof that every collision must expose one.

A stronger boundary-free control has indefinitely extendable older
ancestry. Represent a period-eight temporal profile by an integer whose
bit t is its value at time t. The spatially periodic cycle, older to newer,

    ...202,178,172,43,202,178,172,43,...

obeys every literal Rule30 update. After an occurrence of43, append the
profiles53,42,42. Both OR(43,53) and OR(53,42) equal63. Thus the two
newest42 profiles are equal and unsafe, but their respective parents53
and42 differ. Every displayed actual profile, including the infinite older
cycle, has temporal00. This refutes a boundary-free shielding argument
even when arbitrarily many older unsafe columns are supplied. It has no
white oldest boundary and no oldest differing column; it is not a genuine
finite-white counterexample. Its adjacent twin42 also connects it to the
separate one-history twin classification being investigated by Cedar.

`shielding_controls.py` independently checks every temporal edge in the
four-profile spatial cycle and the three-profile tail using the literal
Rule30 table. These all-time cyclic arguments are paper/computational
controls, not Lean-verified headlines.

For diagnostic scope only, one exact fixed-clock graph was constructed:
period8,209 unsafe profiles,43,681 adjacent states,29,605 edges. Repeatedly
removing states without older predecessors leaves33 states and the explicit
control above. Requiring every ancestor profile to contain BOTH00 and11
at the same clock leaves16 recurrent-ancestry states and no OR collision.
No larger clocks or widths were attempted. The last fact does not prove any
uniform property. In particular, the all-unsafe control contains columns
whose leaf complement is Safe, so a future argument may need both Safe and
co-Safe ancestry information.

## Remaining conclusion

The substantive surviving target is boundary-sensitive: prove that a
two-history nonsaturated OR collision exposes an inadmissible Safe/co-Safe
ancestor, or supply a different descent on the entire return coding. Neither
is proved here. Replacing the white boundary by a fixed band, arbitrarily
long unsafe ancestry, or one complete reset excursion is insufficient.

All statements here concern fixed sheared depth unless explicitly stated
otherwise. A fixed physical observation column samples changing depthU+t.
No result in this directory crosses that sampling gap or proves official P1.
