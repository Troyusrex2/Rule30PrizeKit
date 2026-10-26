# Clock-shift identities and a finite obstruction to cubic reconstruction

The cubic decoder suggested by the preceding finite experiments fails. An
explicit family of 18,528 canonical width-105 rows has even parity for every
head-trace monomial of degree at most three, but odd parity for the
penultimate initial bit. An independent literal Rule 30 simulation checks
all 349,633 such monomials over the full 128-step cycle. Consequently a
Boolean polynomial of degree at most three cannot recover that bit from
arbitrary head-trace samples on every canonical row, even at this width.

**Verification scope:** Lean's unchanged reference checker replayed all
packed orbit and normalized-moment calculations, the connection to the
Rule 30 list update, and canonical ancestry for every phase. The final
generic implication from normalized OR moments to impossibility of every
cubic head polynomial has **not** been formalized in Lean. The direct
head-moment audit and the resulting impossibility argument remain exact
computational evidence, not a complete kernel-checked negative theorem.

The unrestricted `ParentBitObserver`, reader completeness, the fixed-center
bridge, and Prize Problem 1 remain open. No prize submission or Wolfram
backend verification is claimed.

## What the certificate says

Use the preceding canonical seven-state DFA and sheared white-boundary
update `singleStep`. A row's head trace is its final bit under iteration.
The family consists of 290 complete parent cycles, with periods 32 or 64.
Pad each parent to width 104 by leading white cells and append a white head.
There are 18,528 distinct initial rows in the resulting width-105 family.
Each returns after 128 updates. Every initial row is canonical, and Lean
proves that resetting the appended head to white after any parent phase
preserves canonicality.

Let `S` be this family, `c_x(t)` its head traces, and `g_x(0)` its
penultimate initial bits. The independent audit establishes

```
XOR_{x in S} 1 = 0,
XOR_{x in S} product_{t in A} c_x(t) = 0  for 1 <= |A| <= 3,
XOR_{x in S} g_x(0) = 1.
```

The audit tests every subset `A` of `{0,...,127}` of size at most three.
Repeated indices reduce by Boolean idempotence; arbitrary times reduce
modulo 128. Any finite cubic polynomial is an XOR of these monomials, so
its XOR over `S` is zero. It cannot agree with the target on all of `S`.
This is an algebraic obstruction, not a pair of rows with identical traces.
It does not refute a more complex or non-polynomial observer.

The minimized witness is `work/cubic-negative-witness-orbit-min.json`;
its compact cycle description is `work/orbit-negative-certificate.json`.
`audit_cubic_witness.py` uses the literal rule-30 lookup table on arrays of
cells, independently of the packed update and OR-moment calculations. The
latest local run checked 249,016,320 cell updates and every head monomial.
The audit report deliberately retains `Lean_verified: false`.

## Discovery and controls

`clock_cubic_probe.py` exhausts the reachable fixed-clock profile graph,
starting with two all-white profiles. Appending an initial bit integrates
their OR trace when its parity permits the chosen clock. A product with
the canonical parent-prefix DFA retains finite white ancestry. There is
no spatial length cutoff in this graph construction; its temporal clock
is bounded.

At clocks 2, 4, 8, 16 and 32, cubic reconstruction passed. At clock 32 the
2,112 observation profiles already have cubic span of full rank 2,112.
That small case therefore concealed the obstruction.

At clock 64 there are 343,554 reachable product states and 171,776 canonical
OR profiles. The degree-zero-through-three matrix has 43,745 rows and
171,776 columns, occupying 939,292,640 packed bytes. Its rank is 43,745,
but the parent-bit target is outside its row span. A dual witness initially
used 22,208 rows of width 107. Independent literal simulation confirmed it.
Whole-orbit minimization reduced it to the width-105 family above.

The block GF(2) implementation has 70 random matrix/rank/dual controls and
matches the scalar implementation at clocks 8, 16 and 32. Its guarded G913
run took 130.67 seconds and peaked at about 1.22 GB. No guard was raised.
The original and minimized witnesses, reports, code and logs are included.

## Exactly what Lean checked

There are 32 new modules and 301 replayed declarations. All passed the
unchanged checker at kit commit
`0090056412733accaa27643d3cbbf982104f2251`, checker SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The slowest new module took 43.30 seconds including build and replay;
the largest owned process tree used 1,841,106,944 bytes. Each new module
therefore stayed below one minute and 4 GiB.

- `Rule30CubicCertificateData` supplies the 290 packed cycles. Ten orbit
  modules check every transition, return, stored OR/newer profile, and
  initial canonical acceptance. Sixteen moment modules check all 2,080
  normalized triples `(0,a,b)`, with `0 <= a <= b < 64`.
- `Rule30CubicPackedSemanticsV2.parity_semantics` proves that six XOR-shift
  folds equal XOR of the 64 bits. A checked permutation avoids an expensive
  associative/commutative simplification. `stepPacked_matches_rule` proves
  the packed update's agreement with `singleStep` at every valid bit.
- `Rule30CubicOrbitSemantics.packed_iter`, `run_profile` and
  `checked_orbit_is_actual_cycle` connect checked records to actual list
  trajectories and cycles.
- `Rule30CubicCertificateChecked` joins every chunk, checks the target XOR,
  periods and profile bounds, and the phase count 18,528.
- `Rule30CubicPhaseSemantics` proves a general last-bit independence lemma
  for canonical acceptance, canonicality of all parent phases, and that
  each stored profile is an actual Rule 30 profile.

The remaining formal steps are rotation/parity interpretation, cyclic
normalization of triple moments, and the multilinear expansion of a head
trace's XOR integral. These are not silently assumed by a Lean theorem.
The source hashes and per-module results are listed in
`work/publication-inventory.json`. Six preceding dependencies are copied
byte-for-byte with their earlier passing reports.

## New all-time clock identities

`Rule30ClockJetResearch` proves exact plateau identities for consecutive
actual profiles. Write `g,h,k,l` from newest to oldest, with `h`
antiperiodic over `P` and `k` periodic over `P`. Define

```
q(t)   = g(t+P) XOR g(t),
rho(t) = (g OR h)(t+P) XOR (g OR h)(t).
```

Then, at every time,

```
q(t+1) = q(t) XOR NOT k(t),
rho(t) = NOT g(t) XOR (h(t) AND q(t)),
rho(t+1) XOR rho(t) = NOT q(t) AND (h(t+1) XOR h(t)).
```

The mode's flip flag over `P` is the newer profile's flag over `2P`.
These identities constrain the plateau case but do not invert it. In
particular `q` is not asserted to be an actual finite-white row.

All 13 declarations passed full replay; source SHA-256 is
`0cb60f8710596347c6a72753638a4aebeba25b22315a09f498711b0e576660c2`.
Independent Boolean controls and local Wolfram Language 15 built-in
`CellularAutomaton[30,...]` tests passed: 1,022 initial rows, 808
antiperiodic cases and 29,240 comparisons. This is local computation,
not Wolfram review or a backend verdict.

## Failed approaches and refreshed sources

A list-based kernel benchmark hit the unchanged 8 GiB memory guard.
Packed rows and forced evaluation, following the kit's `Rule30Window`,
resolved that failure. A generic commutative parity simplification timed
out on heartbeats; the permutation proof above resolved it. Failed sources
and terminal evidence are retained under `work/failed-attempts`.

Six canonical cyclic SAT queries at clocks 128/256 timed out with
`unknown`. Controls passed, but neither a counterexample nor an
unsatisfiability result was obtained.

The public refresh at 10:19 UTC found 40 entries, no new entries, and
reviewer tags/catalog links added to existing submissions. No new proof
content appeared. No new READY response or changed round-three response
was found in the shared inbox. No external unverified proof was adopted.

The Newton subset/OR-convolution representation is already described in
[Nersissian's diagonal-period paper](https://arxiv.org/pdf/2609.25077);
no novelty is claimed for it. The other primary sources and their limited
relevance are recorded in `work/external-source-audit.json`. Finite-ring
cryptanalytic reconstruction does not supply the missing all-width
canonical white-boundary theorem.

All 2,334 hashes in 33 preceding owned archives were checked unchanged.
This archive advances the evidence and formal tools; it does not solve
the prize problem.
