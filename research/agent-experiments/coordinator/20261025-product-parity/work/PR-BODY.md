Classifies finite-window parity scores of every positive width on any coordinatewise product of Rule 30. Four-step cyclic conservation holds exactly for a constant plus a spatial coboundary, including nonlinear scores mixing two histories. The cyclic formulation constructs a local current as part of the proof, and the converse is included.

This extends the range descent in #21 from scalar integer densities to mod-two product densities. Arbitrary-length preimages with eight trailing white cells give the endpoint rectangle identity; current transport shortens the density until the constant one-cell case. The core-only module uses small kernel-checked Boolean/Fin2 identities and proves the unbounded result by induction. Its semantics theorem identifies the image with exactly four shrinking Rule 30 updates.

The PR adds the module, public import and catalog row. It does not settle a prize problem, exclude nonconservative ranks or nonlocal invariants, or claim literature novelty. A separately checked research companion generalizes the argument to arbitrary additive commutative coefficient groups; this catalog module needs no Mathlib.

Validation at verifier pin 0090056412733accaa27643d3cbbf982104f2251:

- `lake build Ruliology.CellularAutomata.Rule30ProductParity` passes in the core catalog.
- The unchanged official checker accepts all 207 declarations and the four headlines `all_ensembles`, `paired_F2_exact`, `paired_F2` and `paired_F2_semantics`, with no new axioms.
- Cold build plus replay: 13.22 seconds, 0.90 GB sampled peak owned RSS under the ordinary resource guard.
- Independent scalar-ring checks match the preliminary width 1–4 spaces on 5,888 rings. These finite controls are separate from the uniform Lean proof.
