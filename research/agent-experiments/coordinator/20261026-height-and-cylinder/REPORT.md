# Signed heights, a forbidden temporal pattern, and exact limits on ancestry shortcuts

**Five new modules have passed independent root kernel replay. D3*, safety completeness and the Rule 30 Prize remain open.**

The most direct new fact is `CedarNo11011.finite_white_no11011`: for every finite Boolean word and every time, the newest-cell temporal trace cannot contain `11011`. There is no safety, width or clock hypothesis. This is a moving-diagonal trace in the literal finite-white, older-first Rule 30 evolution, not the fixed physical center trace.

The proof first derives a contradiction from four shared two-predecessor OR equations. It then transports the result through arbitrary profiles, handles words shorter than four explicitly, and uses the literal evolution bridge to cover every finite word and time. Thus the conclusion does not rely on guessing a large enough clock or on a bounded SAT search.

## Exact signed-height tools

For Boolean histories satisfying `x(t+1) = x(t) XOR (a(t) OR b(t))`, put Z(t)=1 when a and b are both zero, and E(t)=1 when a, b and x are all zero. Define H_A(T) as the sum of (-1)^t A(t) over t<T, and q(T)=(-1)^T(2[not x(T)]-1). `RootEventHeight.signed_height_identity` proves, for every T,

    2(H_Z(T) - 2 H_E(T)) = q(T) - q(0).

Safety means no successive temporal zeroes of x. Under the recurrence, it makes E identically zero, so H_Z(T) belongs to {0,-q(0)} for every T. The initial sign is retained. An even return time of x gives H_Z=2H_E at that time; no independent period assumption on the drivers is needed. These are exact identities for arbitrary Boolean drivers, not an ancestry classification.

`RootAntiPeriodHeight` applies this identity to a child d driven by b and c, where b has positive even period P and c is antiperiodic at P. It proves the offset-sensitive identity

    H_not_b(T) = H_Z(T) + H_Z(T+P) - H_Z(P).

If d is safe, every difference H_not_b(T)-H_not_b(S) lies between -2 and 2, and H_not_b(P)=0. The zero-drift proof uses the identity at three periods and the integer bound. A nonzero drift, or an interval height increase greater than two, therefore excludes safety. These are necessary conditions; no converse, actual shared ancestry, or monotonicity across spatial columns is asserted.

## The precise remaining safety target

`CedarD3Converse.d3_iff_return_complete` proves equivalence of the explicit D3* ancestry statement and global finite-word safety completeness. The earlier forward implication uses the now-proved short-extension theorem. The new converse uses the exact thirteen-state language bridge and a small transition certificate: a sufficiently long accepted normalized word has an accepted proper prefix after deleting at most three cells.

Both sides of this equivalence remain unproved. D3* says a safe word beginning at its first black cell has a safe prefix one, two or three cells earlier. ReturnComplete says every safe word returns as a whole after eight updates. The equivalence is not an unconditional proof of either side, and neither is being advertised as the fixed-center prize statement.

## Why two attractive shortcuts fail

`CedarTCObstruction.normalized_tc_chain` proves an all-clock obstruction to replacing actual ancestry by a weaker transition-cover relation. Every nonzero Boolean profile with a power-of-two period admits a finite chain from constant one satisfying that relation. The proof uses Delta^(2^k)b(t)=b(t) XOR b(t+2^k), finds the last nonzero derivative, and reverses the derivative chain. It does not supply the actual shared two-predecessor OR recurrence. Thus transition cover alone cannot distinguish genuine finite-white histories.

Root also independently replayed two saved width-ten free-boundary strips with safe newest traces of least periods seventeen and thirty-two. All eight internal columns satisfy the simultaneous recurrence, including wrap; both traces avoid `11011`, yet fail eight-step return. Each has explicit white-boundary failures in the two free input columns. These finite Python checks are diagnostics, not Lean theorems or D3 counterexamples. They show that these particular local strip conditions, even with the new forbidden pattern, do not settle genuine ancestry.

A separate targeted 64-column, 32-clock SAT query was UNSAT. Its core used only the last four recurrence constraints and the target trace, not the white boundary. The target contains `11011`, explaining why this was a local contradiction rather than a useful ancestry test. A known genuine period-32 orbit passed the encoding's positive control. The query was stopped; no larger sweep followed. A local finite-cone control does realize `1101011`, so the singleton obstruction must not be generalized to two-zero clusters.

## Independent validation and scope

| New module | Root-replayed declarations |
|---|---:|
| RootEventHeight | 43 |
| RootAntiPeriodHeight | 26 |
| CedarD3Converse | 8 |
| CedarTCObstruction | 37 |
| CedarNo11011 | 31 |

The 145 declarations include definitions and generated declarations, not 145 distinct mathematical advances. Every headline passed the unchanged official full-replay checker with no new axioms. The pin is `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean is 4.35.0, and checker SHA256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

Root rebuilt these five modules from frozen source bytes in two isolated directories. Dependencies were root's own previously compiled and fully replayed artifacts from the 521-declaration short-extension checkpoint, checked by source and compiled hashes. No peer binaries were reused. Those dependency declarations were not freshly replayed again in this phase. The new height dependency was freshly replayed before its antiperiodic extension. All runs passed the 300-second, 8-GiB-owned and 2-GiB-free guards; exact evidence is retained.

The worker height bundles have fourteen and eighteen independently verified file hashes; Cedar's sealed v03 bundle has 256 verified hashes. Only selected relevant evidence from that bundle is published here. Failed source revisions are retained and clearly separated from the successful final sources. An additional independent worker source/scope review of TC and No11011 passed with no findings; its seven-hash delivery is included. It is not an additional kernel replay. Its separate proposed run-density consequence is paper-only and is not used by any of the verified results.

This is a public research checkpoint. It is not a new catalog PR or prize essay/API submission, a Wolfram backend evaluation, or a claim that the prize has been solved. The next parallel task is a genuine all-width ancestry argument from the carry/100-marker identity; no result from that ongoing work is presumed here.
