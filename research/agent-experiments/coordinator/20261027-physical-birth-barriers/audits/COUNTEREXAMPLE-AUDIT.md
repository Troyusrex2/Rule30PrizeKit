# Independent source, type and scope review — PASS

Reviewed the complete frozen Rule30PeriodicBirthCounterexample.lean, SHA256 f861ad573fa7b079d25cb8ae11fc1401bbe95e49db2c9a328685ac81a7690c40, all ten printed headline types and axiom lists, the complete attempt05 checker output, result/guard receipts, and the two reused dependency mappings. No mathematical or scope gap was found. This review ran no Lean, Wolfram, dynamics, orbit search or duplicate stencil audit.

## Literal configuration and physical lift

All84 literal profiles agree exactly, in order, with the root's saved PHYSICAL-AUDIT.json. They are six-bit values. The separate prior scalar audit checked504 physical stencils and84 pair overlaps; its scope remains scalar evidence, distinct from the new kernel proof.

The Lean definition is orbit(t,p)=bit((t mod6).toNat,(p mod84).toNat), for Int time and Int physical position. Positive moduli give residues in0..5 and0..83 even for negative inputs. The successor/predecessor residue lemmas cover temporal wrap, both spatial wraps, and negative coordinates. Fin6×Fin84 stencils use left=(j+83)%84, center=j, right=(j+1)%84. Hence physical_recurrence is the literal physical Rule30 rule at EVERY integer time and position, not a sheared recurrence or a finite window. List.getD's default cannot affect this lift because every spatial residue is below84 and the literal list has exactly84 entries.

temporal_period6 and spatial_period84 state periods, not minimality. temporal_least6 separately excludes every positive global period below6 using the right-column witnesses. Together they establish least global period6. center_period2 plus center_not_period1 gives least center period2. right_not_period4 has the exact witness t=1,p=1. The source does not claim that84 is the least spatial period; the older scalar audit's stronger numeric observation is not silently promoted to a theorem here.

## Coherent backward shift and endpoints

backwardMismatch(t)=orbit(t,1) XOR orbit(t−4,1) uses Nat subtraction. Its total definition at times below4 is harmless: every birth theorem explicitly uses times at least4. At u=6k+4, the compared times are6k+4 and6k. At u+1 they are6k+5 and6k+1. These identities also hold for k=0, so no truncated-subtraction artifact occurs at the first birth.

The saved right profile is001101 in increasing time order. Thus the phase4 mismatch is0 and the phase5 mismatch is1. orbit_nat_phase transports these exact values to every k. Both compared histories are time shifts of the SAME globally actual orbit; no independent driver or artificial matching of histories is substituted. The center's period2 makes the shift4 center-compatible on all the relevant times.

births_arbitrarily_late chooses u=6B+4 and supplies B≤u and4≤u. linear_birth_witnesses chooses u(i)=6i+4 for i:Fin N. It proves injectivity,4≤u(i), and u(i)+1<6N. For N=0 the quantified domain is empty; for N=1 the readings are4 and5 below6. In general the last start is6N−2 and its next reading is6N−1. The claim about both readings below6N is therefore correct. This theorem is an explicit family of distinct events, not a separately formalized intervalCount identity or logarithmic-budget contradiction.

## Scope and use

initial_support_unbounded explicitly exhibits black sites beyond every positive spatial bound at time zero. Together with the actual spatial period84, the same black phase also repeats arbitrarily far left (a direct mathematical consequence, not an extra headline in this file). The configuration has no finite initial support and no finite-white older boundary. It is not a single-seed history or a counterexample to Rule30 Problem1.

It DOES refute a generic assertion that one nonconstant period-P column forces a full orbit to have period2P: here P=2 while the global least period is6 and the right column fails shift4. It also gives regularly recurring coherent shift4 births, so same-orbit coherence plus a periodic center alone cannot supply the desired subcritical upper birth budget. Any such finite-seed result must use additional ancestry/support information. Adjacent-pair period rigidity is unaffected because this center/right pair has joint period6, not2.

## Validation provenance

The author freshly built this one source and ran the unchanged official checker:44 constants and10 headlines PASS, no new axioms. The source build log is empty; the raw checker retains its existing deprecation warning. Only standard axioms appear in the printed types. Rule30Prize imports the official statements; no changed definitions, new axioms, native_decide, bv_decide, sorry or checker bypass is present. maxHeartbeats0 does not weaken the kernel; the separate process guard remains in force.

Rule30Jen and Rule30Prize objects were reused from the earlier exact7d665 fresh canonical closure, with matching source/object hashes in the receipts. This review checked those mappings without rebuilding them. The earlier failed attempts remain preserved: the transient Unicode-corrupted linear-witness draft and missing dsimp were corrected before the frozen attempt05 source. No failed draft is used as proof evidence.

One minor documentation precision: the author's sealed REPORT describes both dependency source and object checks before and after the run. The replay script checks sources and objects before use, and explicitly rechecks only the object hashes afterward. The independent audit adopts that narrower exact description. This does not affect the proof verdict or require another build; the source dependencies were not mutated by the script.

AUDIT.json records the exact evidence hashes and copies. The independent review is static; the kernel replay claim is attributed to the inspected author receipt.
