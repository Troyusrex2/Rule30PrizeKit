# A finite-clock certificate covering every finite spatial width

Developed by Troy Lowry with OpenAI Codex, 2026-10-24. No prize or priority claim.

The positive result is about the triangular right-moving update Q, not the
vertical center column. If a finite initial state x satisfies Q^16(x)=x,
then any eventual head period H is a period of the entire state: Q^H(x)=x.
The spatial width, head period and transient are arbitrary. The full-clock
bound of sixteen is explicit; no arbitrary-clock induction is proved.

`Rule30FiniteClockCertificateResearch` proves soundness of a generic profile
pool checker. It checks two candidate predecessor profiles for each pair.
If the forcing parity prevents a cyclic predecessor, the proof rules that
case out; otherwise both possible predecessor pairs must remain in the
pool. Induction from the zero tail then covers every finite spatial width.
A separate check propagates a shorter head clock to each next column.
Reduction modulo the full clock handles every natural H, and pure
periodicity removes an arbitrary transient.

`Rule30FiniteClockSixteenResearch` supplies 68 pairs and checks all sixteen
head-clock residues. Both complete modules pass full replay in the working
catalog and the unchanged pinned checker: 85 and 13 declarations, respectively,
with sixteen selected headlines across them. See `finite-clock-evidence`.
The generator reproduces only certificate data; it changes no proof bodies.
There is no native decision procedure, added axiom or modified checker.

Independent Python controls check every word below 2^14, then 128 expanded
words up to width 200. There are 704 checked full-clock-sixteen words,
21,310 profile-pair membership checks and 1,559 head-clock implications.
The Wolfram control checks eight built-in Rule 30 cones against the Q
update: 36,564 scalar cells, all matching.

The result is now included in PR 9 with its exact standalone proof and fresh
LeanLink notebook. Six separate catalog modules replay 349 constants in total;
the combined standalone source replays 345, with 28 selected headlines.
The visible differences are generated matcher/equation names; every other
named declaration is preserved under the documented namespace adaptation.
The entire standalone environment is replayed independently. The notebook
contains five independently checked computation outputs and one diagram,
with no message cells. It has not been sent to the prize API.

## The unbounded step remains open

The certificate does not prove that detection holds at every full clock.
It also does not turn fixed-diagonal clock growth into a vertical-center
nonperiodicity proof. Both gaps remain part of the full investigation.

`clock_onset_sat_probe` tested finite prefixes followed by lower-clock
spatially periodic right tails. Positive controls recover an infinite-tail
period-loss example and a finite clock-doubling example. The corrected loss
query allows the larger clock anywhere inside the prefix: forcing it at
the final column next to a purely periodic tail would make the query
artificially impossible. The corrected small queries are unsatisfiable and
several larger ones reach their five-second limits. These bounded SAT
results are not Lean proofs or unbounded exclusion theorems.

Other tempting simplifications were falsified before use. The parity of the
OR trace is not generally the parity of the head trace, and two initial zero
cells do not prevent period masking in an infinite tail. The finite-support
and full-clock hypotheses must remain explicit.
