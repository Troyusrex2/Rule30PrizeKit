# Agent update: cubic reconstruction fails; the full observer remains open

Use this checkpoint instead of assuming that the cubic success through
width 14 persists. A finite width-105 family defeats every degree-at-most-
three Boolean polynomial in arbitrary head-trace samples. The independent
literal audit covers the entire 128-cycle and all 349,633 head monomials.
The full generic impossibility theorem is not yet formalized in Lean.

Lean has checked all packed cycle/moment facts and their connection to
actual trajectories and canonical phases: 32 new modules, 301 declarations,
unchanged official checker. Read [REPORT.md](REPORT.md) for exact scope.

The open target remains `ParentBitObserver`: for every width, equal head
traces on canonical rows imply equal penultimate initial bits. It is
equivalent to full sound-reader completeness by the preceding checked
reduction. Complexity may grow with the clock; a cubic formula is no
longer a viable uniform template.

Useful experiments or proof ideas:

- Derive a clock-sensitive inverse using finite white ancestry. A local
  plateau band alone is insufficient; a checked counterexample already
  exists without that ancestry.
- Use the new all-time masked shift identities in
  `Rule30ClockJetResearch`. The hidden difference profile need not be an
  actual row. Do not apply actual-image lemmas to it without proof.
- Finish the generic Lean implication from the normalized OR-moment
  certificate to the obstruction for all cubic head polynomials. The
  remaining bridges are listed in the report; this is a bounded obstacle,
  not a proof or disproof of `ParentBitObserver`.
- Seek a structural all-clock argument or a precise falsifiable invariant,
  rather than another finite width census. Fixed sheared depth remains
  different from the physical center column.

Submit each response separately in
`D:\MWB\Rule30\agent-inbox\<unique_response_id>\` with `manifest.json`,
`REPORT.md`, source/evidence and an empty `READY` file written last.
Use the repository's [multi-finding response format](../../RESPONSE_FORMAT.md).
Multiple agents and revisions must use distinct versioned directories;
do not edit another response, this archive or the coordinator checkout.
Label experiments, conjectures, failed attempts and full kernel proofs
separately. Preserve all hypotheses and include exact checker evidence.
