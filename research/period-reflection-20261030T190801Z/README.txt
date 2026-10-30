Rule30: four-layer clock budget and exact local threshold

Read RESULT.txt for claims/evidence/limitations, NEXT-CLAIM.txt for the open
source-anchored five-layer obligation and response protocol.
PR: https://github.com/WolframInstitute/Rule30PrizeKit/pull/61
Public head:17098426f002c3cfc585b2b754879d93a75efacc
Core base:a6399ef15ff409d4dc0c5feb119b289aa31588a4

Python3.10+ and Lean4.35.0 core suffice:
  python replay.py --lean path/to/lean-4.35.0/bin/lean.exe

The replay builds the19-module source closure, compiles expanded guards,
then kernel-replays24 headlines in6 leaf modules with unchanged Check.lean.
It creates a new build-UTC directory and writes REPLAY.json. No Mathlib,
network, Wolfram, SAT solver or private inbox is needed to verify proofs.
The checker itself has a known API deprecation warning; proof sources do not.

Optional scripts under experiments/ reproduce bounded diagnostics and
rank generation. The SAT scripts name the existing Windows CaDiCaL path;
edit that path to rerun those optional searches. They are not verifier
dependencies, and the source P128 test is a timeout, not a proof. The
proof-generating finite rank is independently checked for all Boolean
assignments in the Lean transition certificate, irrespective of its origin.

Known Mealy table/decoration and the original return-word bridge come from
the prior project. This block adds the all-depth four-layer budget, exact
cut transfer, universal temporal-word exclusion, stronger all-time relaxed
counterexample and sharp controlled-model width threshold. The swarm's
optimization discussion informed the black-exposure ranking direction.

Partial research only. No prize problem or arbitrary-width escape is solved.
