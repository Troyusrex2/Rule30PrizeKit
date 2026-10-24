# Catalog contribution and further general lemmas

The four-tail completion is published on the separate catalog branch
`research/stripe-tail13-complete-20261024`, commit `7de67a4`. It adds only
32 core certificate modules, the theorem module, its umbrella import, and
catalog documentation. The five-tail extension remains a separate research
bridge to Quint/Gemini's verified submission.

Fresh replay of the catalog-format sources at reference commit
`3eca23c0a9fa6b153313655e6d51835406c2d06e` passes all 33 modules and
564 declarations, with the unchanged official checker and standard axioms.
All 33 normal module builds pass, and the complete 154-job core catalog build
passes. The first aggregate build hit its 300-second guard on the pre-existing
`WhitePaddingFamilies` certificate. That dependency passed in isolation in
289.234 seconds; the resumed aggregate build passed in 113.391 seconds.
See `tail13-catalog-evidence/report.json` and `normal-build.json`.

Two additional research modules now provide general tools, without a claim
that arbitrary finite tails have successful certificates:

- `Rule30FrontLiftResearch`: 23 declarations / seven headlines replayed.
  `punctured_cycle_lift` combines a smaller cycle's successful residues with
  explicit larger-width checks on the exceptional residue lifts. Both the
  higher period and those exceptional checks are premises.
- `Rule30FrontPeriodLiftResearch`: 37 declarations / eight headlines replayed.
  Flipping the highest input bit commutes with the finite front map. A lower
  window return after `L` steps yields a one-bit-larger return after `2L`.
  Every width `w >= 1` has the uniform return period `2^w` for every fitting
  initial window and phase zero or one. These theorems prove return only;
  they do not prove the white-witness condition.

The new `jump_table.py` pilot simulates all 4096 upper 12-bit inputs over a
fixed width-34 lower cycle together. Its return map has a 32-state zero orbit;
all 32 previously exceptional lifts pass the width-46 test. Sixty-four scalar
controls agree. This may replace the two-million-step proof with a smaller
parallel return-map certificate, but its parallel semantics have **not yet
been proved in Lean**. The sparse low-degree appearance also disappears in
higher output bits: the top tested correction has degree nine and 709 terms.

The three-state Mealy model in `mealy_probe.py` matches the integer map in
the recorded controls, but self-composition grows from three states to over
57,000 states at the sixteenth power. Its next composition hits the 100,000
state cap. This has not provided a fast general power algorithm or a proof
of center-column nonperiodicity.

Problem 1 and Q01 remain open. No new prize API notebook has been submitted.
