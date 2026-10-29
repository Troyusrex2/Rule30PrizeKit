Rule30: actual-seed Hankel cancellation and endpoint-control diagnostics
Research by Troy Lowry, bounded block on 2026-10-29.

NO PRIZE SOLUTION. No new unconditional period exclusion is asserted here.
This archive makes exact failed candidates, reusable identities, and a
separate unformalized paper argument available without portraying finite
rank growth or local reset tests as a proof of the center's aperiodicity.

VERIFIED LEAN CONTENT

HankelSourceResearch.lean:
- Actual single-seed counterexample to the proposed fresh-source pivot
  implication: H2 is invertible over F2, the newest nonlinear source is 1,
  and H3 is singular. An older source cancels the newest source.
- The same third integer Hankel determinant is -2; the integer H8 has a
  displayed nonzero nullvector. These are small exact controls, not a new
  numerical lower bound or an asymptotic theorem.
- Exact two-step parity identities; the coarse row does not evolve by a
  closed Rule30 recurrence without the other parity track.
- Uniform finite-horizon Rule150 impulse-arrival aliasing: sources on one
  backward characteristic have identical responses through first arrival.
  This does not assert equality of their later responses.

NewtonHankel.lean:
- Classical binomial/Pascal congruence H(Tf)=P H(f) P^T and determinant
  invariance. These identities are not claimed as new mathematics.
- The exact actual-seed transformed dynamics: Rule90 plus a binomially
  weighted adjacent-product history.
- The transform is involutive over F2. Even/odd decimation identities for
  the transform and the transported source product hold at EVERY index.
- A newest-neighbor perturbation remains masked by the actual center.
  The coordinate change therefore does not remove the observability issue.

EndpointTransport.lean:
- Arbitrary finite middle-word reconstruction with two white right registers.
- A uniform endpoint-rectangle identity and its obstruction to separable
  fluxes for a normalized density with a genuine endpoint interaction.
- The single-site normalized local-flux base case is trivial.

EndpointCountermodel.lean:
- The endpoint property holds for every left XOR g rule with g(false,r)=r.
- Rule210 satisfies it at all word lengths while its single-seed center
  is eventually white. The center210 fact is imported from the official
  Rule30Realization module, not newly claimed here.
- Consequently this global endpoint property alone cannot imply seed
  aperiodicity. A source/rank argument must add an actual-seed bridge.

ResetCountermodel.lean:
- The exact spatial register word 0101 sends all four register states to
  one state. The alternating Rule30 ether is fixed and contains disjoint
  copies at all times while its center is constant.
- More strongly, for EVERY horizon T and requested count K there is a
  FINITE-SUPPORT start whose center is constantly black through T and whose
  next rows through that horizon contain K disjoint copies of 0101.
- This is a uniform finite-prefix counterfamily. It does not refute the
  proposed asymptotic singleton-seed Hankel bound; it shows precisely why a
  generic finite reset count cannot by itself force rank growth.

COMPUTATIONAL AND PAPER CONTENT

experiments/ contains fixed-limit tests and exact results. The primary
pivot computation has an independent Wolfram CellularAutomaton control.
The local F2 conservation-law search finds only constants/coboundaries
through density width 8; Wolfram MatrixRank independently agrees through 6.
All 274 nonzero normalized densities of nominal width <=4 satisfy the
predicted span-growth check. These computations are not Lean proofs.

COHOMOLOGY-UNIFORM-ARGUMENT.txt gives a proposed all-width ANF/shape argument
excluding nontrivial local additive F2 conserved charges, with exact review
obligations. Only the stated endpoint ingredients and single-site base case
are formalized. No claim is made that the full classification is checked or
new. The argument would also apply to Rule210 and hence would not solve the
single-seed center problem.

REPLAY

Requires Python3, official Lean4.35.0, and an ALREADY PREPARED Mathlib package
cache pinned to 56a005855ea17e0b0958f73ec801ae140b0a1679. No downloader or
package installation is run by this verifier. Example on this machine:

python verify.py --lean D:/MWB/Rule30/toolchain/lean-4.35.0-windows/bin/lean.exe --mathlib-packages D:/MWB/Rule30/deeper-padding/.lake/packages --out <a-new-empty-output-path>

The three official core modules are frozen byte-for-byte from kit commit
932cf8dde039b89b1dcbe9636867bb1b2057fef0. Every owned .olean is rebuilt from
source in the newly created output. The unchanged official Check.lean
replays each owned module and checks the selected partial headlines for
standard axioms. Mathlib dependencies are cached, not rebuilt cold. This is
not a whole-catalog build. The checker itself emits one deprecation warning;
owned source builds must be warning-free.

Partial mode accepts arbitrary theorem types, so a checker pass does not
certify a prize implication or mathematical novelty. The statements in the
sources determine exactly what was proved. verification/ contains the
recorded replay result and logs; INPUT-HASHES.json freezes the replay inputs.

SOURCE CREDIT AND PUBLICATION STATUS

The packed row adapter in HankelSourceResearch is copied/adapted from the
official Rule30Window.row_testBit development and is credited in the source.
Official Jen/Realization results are reused with their original provenance.
Standard Hankel and binomial identities are infrastructure, not new claims.

The distinct arbitrary-driver effective-boundary transport result is
submitted for catalog review as https://github.com/WolframInstitute/Rule30PrizeKit/pull/57 .
Its PeriodicMaskExclusion hypothesis is OPEN. This research archive is not
another catalog PR and is not a formal Wolfram prize submission.
