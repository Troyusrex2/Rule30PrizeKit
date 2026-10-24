# A checked parallel return-map certificate

The previously completed tail-13 family now has a second Lean proof using a
parallel return map. This is a verification method and a proof of the same
family, not a new solution of Q01 or Problem 1. It does not import the earlier
two-million-step complete-cycle certificate.

For the width-34 front map, the independently replayed Quint/Gemini submission
[R30-20261024-f177ae](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261024-f177ae)
proves return after 65,536 steps and successful white-witness tests at every
required residue except 61,005. We simulate all 4,096 possible upper 12-bit
inputs in parallel, over that one lower cycle. Nine closed execution checks
link the proposed checkpoint constants to Lean's actual front iteration.

The induced upper return map has a 32-step orbit from zero. At the exceptional
lower residue, all 32 lifted states pass the width-46 white-witness test.
The generic `punctured_cycle_lift` lemma then gives the complete period
2,097,152 certificate. `compressed_row4_13` proves that every odd stripe-prefix
length `m` in this family has an even-time white witness by `m + 45`.

## What the kernel checks

`Rule30FrontLanesResearch.lean` proves generic bit-parallel semantics, not just
the particular data. Its `initial_run_correct` identifies each projected lane
with the official finite front orbit, for every time and fitting initial
window. The source has 155 declarations and 22 checked headlines.

The 11 execution modules under `front-jump/` have 32 declarations in total;
the table-property module has 17, and the final cycle module has 23. All 227
declarations in these 14 new modules passed the unchanged official checker's
full kernel replay. The external lower-cycle proof was separately replayed
(363 declarations), as were both general lifting modules (23 and 37).
Only standard axioms are accepted. No Python value is an axiom or premise.

`Rule30FrontReturnMapResearch.lean` separately generalizes the composition step
to arbitrary widths, embeddings, finite return maps and exceptional sets. Its
five headlines and all ten declarations pass kernel replay. The headline
`return_map_cycle_lift` assumes a checked return-map cycle and the exceptional
witness checks; it does not assert their existence for an arbitrary tail.

Evidence is in `front-lanes-evidence/report.json`, `front-jump/evidence/`,
`front-jump/map-evidence/report.json`, and `front-jump/cycle-evidence/report.json`.
The general theorem's report is `front-return-map-evidence/report.json`.
The reference commit is `3eca23c0a9fa6b153313655e6d51835406c2d06e`.

## Reproduce

Prepare the kit at that exact commit with Lean 4.35.0 and its dependencies.
Keep this directory inside the research repository, which supplies the resource
guard. Python needs `psutil`; the checked proof does not require NumPy or a
learning library. From this directory:

```
python replay_compressed.py --project /path/to/pinned-kit --lake /path/to/lake
```

The pipeline obtains the attributed external source from its public submission
if absent, verifies its SHA-256, builds each dependency in order, and replays
every module. It refuses a different project pin, a changed `Check.lean`, or
a conflicting owned source file. Each compiler/replay job retains a 300-second,
8-GiB owned-process-tree, 2-GiB-free-memory limit. `--resume-endpoints` is optional
and retains only matching endpoint sources, passing reports, and objects.

`generate_front_jump.py` proposes the constants; it does not establish their
correctness. Regeneration is optional, and should precede a fresh full replay.

## Further experiments and limits

The fixed 4,096-state return table has no separating invariant of algebraic
degree at most eight under the constraints tested in `learn_jump_invariant.py`.
An exact GF(2) solve finds one at degree nine with 1,244 terms. This is finite
Python evidence, not an all-width impossibility theorem or a useful simple
invariant.

`learn_jump_vector.py` also tests a vector of invariant polynomials. At degree
eight, the bad state 928 still shares every such invariant with zero, so a
nonlinear classifier of those features cannot repair this particular failure.
At degree nine, the greedy construction selects six invariants totaling 6,801
terms, a more complicated finite separator than the scalar solution. Neither
learning experiment has produced a useful uniform rule. These are exact finite
linear-algebra computations in Python, not Lean impossibility theorems.

`jump_degree_barrier.py` emits and independently replays a dual certificate
for the degree-eight obstruction: a sum of return-map edge differences equals
the difference of the monomial feature vectors at zero and 928. Its vertex
parity is a cubic Boolean polynomial; all 3,797 required monomial moments
are independently checked. This strengthens the finite audit trail, without
turning it into an all-width result or a Lean theorem.

For tail 131, arrival 32,379,339 previously survived the 72-step test. A two-limb
simulation and an independent arbitrary-precision simulation agree on a white
witness 73 steps after arrival, at absolute even time 32,379,412. A subsequent
width-74 scan returns after 1,073,741,824 steps with no bad required residues.
These latter results are numerical only; they have not been kernel certified.
They neither establish an arbitrary-tail theorem nor refute Q01.

The earlier tail-13 catalog contribution remains
[upstream PR #15](https://github.com/WolframInstitute/Rule30PrizeKit/pull/15).
This research follow-up changes no claim about prize status. No new prize API
notebook was submitted.
