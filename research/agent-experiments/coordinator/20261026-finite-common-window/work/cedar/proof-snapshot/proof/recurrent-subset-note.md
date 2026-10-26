# Recurrence does not supply finite-prefix Subset preservation

Status: independent paper analysis of one proposed lemma and the supplied
width-four control. No new search, horizon sweep, formalization, or kernel
result is claimed. Earlier checkpoints remain unchanged.

## Definitions and the proposed finite-prefix route

Use the genuine white older boundary and the exact definitions from
Rule30CommonPastResearch. For row functions A,B,H, put D=A XOR B. Actual
rows follow F. Mode follows

    H'_0 = H_0,
    H'_1 = H_1 XOR H_0,
    H'_j = H_j XOR ((NOT B_(j-2)) AND H_(j-1))
                    XOR ((NOT A_(j-1)) AND H_(j-2)), j>=2.

Common on an adjacent pair j,j+1 means

    D_j AND H_(j+1) = H_j AND D_(j+1).

Subset on a row means H_j AND D_j = H_j at every specified position.
On a finite prefix of width N, internal Common checks j=0,...,N-2.
It does not impose the additional pair crossing from N-1 to N.

The tested lemma was: for every finite prefix, with actual A/B and mode H
one-step updates and internal Common in both rows, output Subset implies
input Subset. This lemma would suffice for the proposed recurrence route.
Indeed the existing actual_periodic and mode_periodic theorems give each
coordinate j the period2^j, independently of Common. Thus a fixed width-N
joint prefix returns after L=2^(N-1) for N>=1. Given initial Subset, for
any target time t choose a multiple mL>=t. Subset holds again on this
prefix at mL. Repeated application of the proposed backward lemma, using
all-time internal Common, would carry it back to t. This conditional
recurrence argument is logically valid; its backward lemma is false.

## Exact width-four counterexample

Integers use bit0 for the oldest cell. The genuine white update gives

    (A,B,H) = (1,2,8)  -->  (7,14,8).

The difference changes from3 to9. H is supported at position3, absent
from input difference3 and present in output difference9. Subset therefore
fails before the step and holds afterward. Internal Common holds in both
rows: H_0=H_1=H_2=0, and D_2=0 is the only additional requirement.

There is a stronger full finite-prefix recurrence control. The four phases
are

| phase | A | B | H | D=A XOR B | Subset |
|---|---:|---:|---:|---:|---|
|0|1|2|8|3|false|
|1|7|14|8|9|true|
|2|9|2|8|11|true|
|3|15|14|8|1|false|

The next phase is0. Each A transition follows F, B alternates2/14, and H
remains8 because all older mode bits vanish. D_2=0 at all four phases, so
internal Common holds for every natural time. Starting at phase1 gives
initial Subset, recurrent genuine white finite prefixes, and all-time
internal Common, yet Subset fails two steps later. Thus recurrence alone
cannot repair finite-prefix truncation of the Common hypothesis.

## Exact half-line limitation

This is not a counterexample to the problem with Common at every adjacent
pair on the whole half-line. Zero-padding the input rows(1,2,8) gives the
full output rows(7,14,56), rather than(7,14,8): the mode propagates to
positions4 and5. Output Subset fails at those new positions, and Common
already fails on the output pair3,4. The finite-prefix cut discarded
precisely such newer constraints.

Even if a backward lemma with WHOLE-half-line output Subset and Common
were available, the cited recurrence argument would not automatically
supply its premise. Coordinatewise periods2^j give simultaneous return
of every fixed finite prefix, not a common return time for the entire
half-line. A proof must either localize the backward implication to a
valid finite hypothesis or provide its genuinely global future premise.
The disproved finite-prefix lemma does neither.

The existing theorem subset_from_future has the hypothesis

    for every t>=T and every j, SubAt(t,j).

It is not a theorem from Subset on one later row, on a recurrent sequence
of separate finite prefixes, or at the initial row. Its periodic-property
argument legitimately transports an all-future hypothesis backward; that
hypothesis remains stronger than the desired preservation statement.

## Provenance

Definitions and recurrence statements were read from
D:/MWB/Rule30/overnight-20261024/research/agent-experiments/coordinator/20261026-common-past/work/Rule30CommonPastResearch.lean.
The coordinator supplied the exact width-four candidate and orbit; this
worker checked every displayed identity algebraically. The structural
worker independently audited the literal finite transitions, complete
four-cycle wrap, and half-line zero-padding distinction in
../structural/recurrent-subset-probe/{audit.json,cycle-audit.json}, with
sources audit_candidate.py and audit_cycle.py in that directory. All
supplied checks passed. No broader alternative search was performed after
this counterexample.
