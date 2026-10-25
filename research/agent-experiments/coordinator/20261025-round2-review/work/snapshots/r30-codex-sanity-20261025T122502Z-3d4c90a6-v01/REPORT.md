# R2-03: nonlinear source minors after the matrix-search failure

Response ID: r30-codex-sanity-20261025T122502Z-3d4c90a6-v01
Agent: codex-sanity, Codex. Campaign: rule30-20261024.
Original response: r30-codex-sanity-20261024T214837Z-5d3c83fc-v01.
Supersedes: none; this is a new experiment, and the original remains intact.
Research base: 102d5b8e938b031a6d4df53541d9da2c50ffb859.
Round-two handoff: e8b3475582739991911bc0444d2d1689d513a27b.
Reference verifier: 3eca23c0a9fa6b153313655e6d51835406c2d06e, Lean 4.35.0.
No Lean build, checker run, or Wolfram verification is claimed for this response.

## Batch overview

The coordinator's 100,000 unsuccessful sampled matrix assignments motivated
a structural change, not more random matrices. The useful candidate is an
unbounded-size GF(2) matrix of nonlinear source parities at separated binary
scales. Its entries are derived from actual single-seed spacetime.

There are three independent classifications:

| Finding | Status | Result |
|---|---|---|
| F001 | FAILED | A bounded-rank substitute cannot satisfy the old three-observation strict-descent rule. A pigeonhole argument covers every fixed rank bound; exact seed witnesses cover bounds 1,2,3. |
| F002 | EXPERIMENT | A dyadic specialization of the known Duhamel identity gives explicit source-parity matrix entries. Unbounded rank would imply official Problem 1. The missing growth lemma remains open. |
| F003 | FAILED | Natural stronger growth guesses fail: time-monotonicity drops rank 1 to 0, and the proposed near-full square family already fails at size 3. |

Problem 1 is not solved. No claimed fraction of progress, new prize essay,
or claim of new Wolfram approval accompanies this package.

## Conventions and prior-work check

Use physical Rule 30, new=left XOR (center OR right), a single black cell at
position zero, white exterior, and time starting at zero. In the integer
frame physical position p at time t is bit t-p. Therefore Phi(a)=a XOR
((a<<1) OR (a<<2)) and c(t)=bit(Phi^t(1),t).

The kit catalog already records both Duhamel's formula and Hankel-rank
equivalents. I read the relevant CenterFormulas source and do not claim
either as new. The public submission index was refreshed (45 entries;
updated 2026-10-25T12:26:08Z), with a title census and source inspection of
the relevant cut-rank submission R30-20261025-bcf514. Its generic RankMax
reduction does not prove rank growth for Rule 30. Our matrix selects powers-
of-two columns from a cut matrix and subtracts its zero column; the proposed
additional mechanism is the explicit nonlinear source representation.
No exhaustive novelty claim or reliance on an unreplayed public proof is made.

## F001: fixed-size matrix rank cannot replace the old score

- Track/status: H / FAILED. Verification: finite computation plus a written
  general argument, not kernel replay.
- Failed proposition: a score R in 0..B strictly decreases after two steps
  whenever three consecutive observations agree, for every canonical pair
  (Phi^T(1)<<P, Phi^(T+P)(1), T+P), T>=0,P>=1.
- Mechanism of failure: any infinite binary sequence has two equal blocks
  of length 2(B+1)+1. Their overlapping three-bit guards demand B+1 strict
  decreases. DERIVATIONS.md gives the proof and canonical-pair bridge.
- Decisive finite witness for B=2: T=1,P=25; both seven-bit blocks are
  1011100. At T=1,3,5 the guards require rank values r0>r1>r2>r3, impossible
  if r0<=2. Exact integers and observations are preserved in results.json.
- Scope: all fixed-dimension matrix ranks over any field, and every uniformly
  bounded natural score under this guard. This is separate from the new
  absorbing-prefix barrier and needs no ether assumption.
- Limitations: this does not refute our original unbounded integer
  off-diagonal score, growing matrix dimensions, or all matrix methods.
- Next action: stop fitting bounded rank to that descent specification.
  If useful, formalize the short pigeonhole obstruction before another search.
- Dependencies/conflicts: none. The prior response supplies context, not a
  proved premise; its unbounded score is not contradicted by this finding.
- Evidence: A002, A003, A005, A006, A007, A008.

## F002: separated binary scales expose nonlinear source minors

- Track/status: E / EXPERIMENT. Verification: exact finite computation and
  explicit derivation; no formal unbounded result.
- Exact construction: for 2^K>T+n-1, form the n-by-n matrix

      M(T,n,K)[i,j] = c(T+i+2^(K+j)) XOR c(T+i).

  The crucial identity expresses each entry as a parity sum of actual
  adjacent-black products under an explicit complementary-binary-digit
  propagation kernel. Equations (1)-(5) in DERIVATIONS.md specify it fully.
  The linear Rule 150 contribution cancels by finite support and Frobenius;
  the OR product supplies the remaining terms.
- Exact missing lemma U: for every r>=1, there exist n,K with 2^K>n-1 and
  rank M(0,n,K)>=r. An eventual period P after T0 would bound all these ranks
  by T0+P, since all later rows repeat modulo P. Thus U would imply the
  exact official Problem 1, including all periods and onsets. U is unproved;
  neither the identity nor the rank table below supplies it.
- Falsification and observed result: two implementations agreed on all
  32,780 center bits, and a physical-coordinate simulator independently
  checked 193 times for each of Rules 30,90,150,210. The block identity
  passed 760 exact cases: 0<=t<32, 0<=k<7, 1<=P<=8, 2^k>t, q=P*2^k,
  within the recorded 1,024-step source buffer.

  For T=0, K=ceil(log2 n), n=1..12, the ranks were:

      0, 1, 1, 3, 5, 6, 6, 7, 8, 10, 10, 11.

  Results include each matrix and an invertible minor, checked by forming
  its inverse and multiplying back to the identity. Rank 11 at n=12 is
  finite evidence only. No matrices or weights were fitted to these data.
- Cancellation control: at t=0,q=4, source-time contributions j=1 and j=3
  cancel. The actual period-seven ether table likewise has nonempty source
  sums canceling over 28 steps. The finite right half 0x6b70 under the
  official alternating boundary produced the known 0101... free stream
  for 512 checked bits and rank zero. That driven half is not the seed;
  the finite-row support argument is not transferred to it.
- Other controls: the matched 5-by-5 matrices for Rules 90,150,210 have ranks
  1,0,1; digit-parity (Thue-Morse) gives rank one. Mere nonlinear activity,
  binary structure, or many source events is insufficient.
- Barrier check: the dimensions grow, and entries read actual spacetime
  cones. This is not an absorbing reader's additive geometric prefix score,
  nor a score asserted to decrease at every step. Escaping those hypotheses
  is not evidence that the new lemma holds.
- Next action: attempt an ancestry-based odd-minor construction using the
  explicit binary-carry kernel, with a pairing that leaves an odd residual.
  The exact missing statement is in DERIVATIONS.md. Do not substitute
  path existence, extrapolated ranks, or a larger trace for that argument.
- Dependencies/conflicts: no external proof dependencies. Duhamel was
  rederived here in the packed frame; catalog sources were read, not replayed.
- Evidence: A001-A010 as applicable; mathematical derivation A002,
  computation A003/A005-A008, provenance A009/A010.

## F003: stronger rank-growth shortcuts fail on the actual seed

- Track/status: E / FAILED. Verification: exact finite computation.
- Failed strengthening 1: M(T,n,K) has nondecreasing rank as T advances while
  2^K>T+n-1. At n=2,K=8 the matrices for T=0 and T=1 are respectively

      [0 1]       [0 0]
      [0 0]  and  [0 0],

  so the rank falls from 1 to 0. All entries use the actual seed center.
- Failed strengthening 2: rank M(0,n,ceil(log2 n)) >= n-1 for every n>=2.
  At n=3,K=2 the rows are 000,001,000: rank 1 < 2. Full rank fails too.
  Columns in these displayed bit strings run from the smallest shift upward.
- Scope: these two proposed shortcuts only. They do not refute U or imply a
  bounded eventual rank. The matrices at changing K are not nested.
- Barrier/cancellation meaning: neither monotonicity nor a pivot at each
  selected size follows from local nonlinearity. F001 gives a different,
  general obstruction to bounded descending scores.
- Next action: retain the failures as mandatory controls for any parity/pivot
  proof. A successful claim must allow delayed rank gains and adapt its minor.
- Dependency: this response's F002 defines M; no truth of its growth lemma
  is assumed. No conflict with an existing published finding is asserted.
- Evidence: A002, A003, A005-A008.

## Reproduction, limits, and delivery

Source is self-contained Python except psutil for the guard. Versions used:
Python 3.12.3, psutil 5.9.8. From this response directory run:

    python src/run_guarded.py --output <a-new-output-directory>

The output directory must not exist. The script writes center.bits,
results.json, the raw run log, and resource metadata there, preserving this
completed response. Assertions cover truth tables, coordinates, exact source
identities, matrix-minor inverses, and the stated controls. No optimization
solver, training, GPU job, or paid service is used.

The final guarded run completed in 1.469 seconds; sampled peak owned RSS was
22,319,104 bytes. Limits were 300 seconds, 8 GiB owned-tree RSS, and at least
2 GiB system memory available. Samples are not a guaranteed true peak. The
guard reports failure/unknown on limits or errors. No timeout or numerical
error occurred. Reproduction time may differ; hashes of actual final source
and artifacts are in manifest.json.

No source or build output in the shared reference or another agent's folder
was edited. This response was developed in its own clone at the research
base. Local delivery is to its unique agent-inbox directory, READY last.
This records coordinator intake readiness, not confirmation anyone read it.
