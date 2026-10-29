# Exact finite-past closing experiments

Let a_G(2r)=!G(r), a_G(2r+1)=true, with every little-endian8-cell gate window in S={8,9,16,18,33,36,66,72,132,144}. Let recon be official Rule30ZeroBoundary.recon, lam(a)(k)=recon(a)(k,0). Given two legal n-bit pasts p,q followed by the same G, their temporal boundaries agree for t>=2n.

At a spatial column k, record every temporal value at0<=t<2n. If these records agree across ALL legal p,q at both k-1 and k, then they agree at every later column. Indeed the shared future gives equality for t>=2n at every spatial position (recon_local), and the inverse Rule30 recurrence computes column k+1 from k,k-1 and time t+1. Induction on spatial position propagates the equal pairs. Thus a finite prefix of G can certify agreement for every infinite continuation.

`strip.py` explores all ten initial legal8-cell future words, appends a bit only if its new8-window is legal, and prunes a branch only at this absorbing pair condition. `audit.py` separately verifies that the terminal prefixes form a prefix-free, complete cover of every legal infinite future, enumerates all2^n possible pasts using cross-window tests, and replays literal Rule30 truth-table inversion on shrinking finite triangles. No periodic future is assumed in a completed cover.

Completed computational covers:

|Past length n|Maximum equal-pair second column|Terminal prefixes|
|---|---:|---:|
|3|21|10|
|4|39|13|
|5|50|17|
|6|100|36|
|7|108|71|
|8|155|175|
|9|177|423|
|10|235|1064|
|11|271|2473|
|12|289|5907|

Equality actually starts one column before the second-column value in this table. These are sufficient cover bounds, not a claim of globally optimal closing delays. All covers were independently replayed, including576,783,724 literal inverse-cell checks for n12. They are computational certificates, not yet Lean theorems. The fixed three-bit case was already proved in PR47; the new computation extends the tested range, not the arbitrary-n theorem.

The candidate universal bound20n is false. At n10, future prefix length100, future word654331177868800777882986221700, past codes132 and528 produce different row0 values at column200. The prescribed future can continue with repeating bits00001; all three complete gate sequences are legal. An independent literal replay also found analogous rate counterexamples for n11 and12. These do NOT refute eventual tail equality. In fact the eventual-gap5 future lies in the subclass covered by the previously proved periodic-tail theorem. A new Lean source is checking the n10 rate counterexample and the absorbing-pair lemma.

The remaining target is a finite closing delay for every n and arbitrary legal G. A handful of complete finite covers, a fitted rate, or periodic-future density does not prove it. The exact relation between an arbitrary-n result and the finite-support Prize bridge also remains to be completed.
