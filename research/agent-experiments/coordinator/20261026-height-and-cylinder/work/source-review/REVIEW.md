# Source and scope review: PASS

No semantic defect was found in the two exact sources below. This is an independent source review, not another Lean build or checker replay. Root is handling independent kernel replay. The source snapshots in this folder are byte-identical to the reviewed Cedar files.

| Source | SHA256 |
|---|---|
| CedarTCObstruction.lean | `2137d6db0e2890e59d49f2bf75dc9c32c62271bef354c35e2dbf7f8d91dd83ca` |
| CedarNo11011.lean | `951a3da95ec9e2b11a58ea3aa677e405e4666277acaf8fda5dd52fd27a059d9e` |

## Transition-cover obstruction

`normalized_tc_chain` has the claimed exact hypotheses: a Boolean profile on Nat returning after 2^k steps, and nonzeroness. Its conclusion supplies a finite chain from constant one to the requested terminal profile. Every chain profile has that returning period, each adjacent derivative equals the preceding profile, and hence each pair satisfies the two transition-cover inclusions.

The derivative iteration identity is correct in characteristic two; exact returning periodicity annihilates the 2^k-th derivative. The finite descent then finds a nonzero derivative with derivative zero, which is constant one on Nat. Reversing the finite derivative sequence gives the normalized chain. Both k=0 and the length-zero m=0 chain are correctly covered. The function x is defined beyond m by truncated subtraction, but the adjacency conclusions are explicitly restricted to i<m, so no additional transition is silently claimed.

Crucially, this does not supply the actual shared two-predecessor equation Delta x_(i+1)=x_i OR x_(i-1). The theorem therefore rules out using transition cover alone as a sufficient ancestry test. It is not a finite-white orbit construction, a D3* counterexample, or a proof about the fixed physical center.

The source separately proves constant-white compatibility and white-to-constant-black compatibility. Arbitrary leading-white padding of the normalized chain is an immediate paper consequence, not an explicit conclusion of the main chain theorem. Extension from Nat profiles to integer time by periodic residues, and the explicit Safe terminal-profile/triple-event examples discussed in the accompanying Cedar report, are also paper consequences rather than named theorems in this module.

## No11011 local and literal-evolution bridge

`local_no11011` uses four genuinely shared OR equations, not four unrelated transition-cover witnesses. Its six traces B,A,u,v,w,z overlap exactly as required. It only needs recurrence times0..3 and rules out B values11011 at times0..4. The two A(1) cases both give direct Boolean contradictions with those same shared predecessors. No period, Safe, white-boundary or normalization assumption is hidden in the local argument.

`four_profile_no11011` generates exactly four successive profiles from arbitrary older profile inputs p,r. `next_profile_step4` uses the previously proved exact profile recurrence only at times below4, safely within its below8 limit. The spatial induction for longer words updates the two boundary profiles together, preserving their shared identity. It does not substitute separately chosen older witnesses at different equations.

The final white-boundary specialization explicitly handles all15 words of lengths0..3. In particular, the empty word's newest default is false; it is neither dropped nor assigned an artificial black value. The exact `trace_white` bridge is used only at times0..4, within its proved bound of8. Arbitrary starting time is obtained by restarting the literal finite-white evolution from `evolution t xs` and using the semigroup identity. No finite temporal window is being substituted for an all-time assumption.

The dependency hashes for CedarSafetySoundness and CedarSafetySemantics match the already reviewed immutable F003 delivery, including the definitions of F, evolution, profileTrace, newest and the default-white boundary.

`finite_white_no11011` is an all-width/all-start-time theorem for the newest coordinate of a finite older-first prefix. Prefix autonomy supplies the analogous statement for any spatial prefix coordinate, but that corollary is not explicitly named in this file. These are the moving-diagonal coordinates used throughout this research. No fixed physical-center assertion, return8 conclusion, D3* implication, or trace-classification theorem follows from this module alone.

## Verification status

Cedar's accompanying reports record successful full replays of37 declarations for TC and31 for No11011. Those are producer-reported checks. This review did not rerun them and does not count them as additional independent replay. Root's fresh replay should be the acceptance gate for use of the two modules. The next suggested implication in NEXT_IMPLICATION.md is a paper argument only and has not been formalized.

No Cedar file, shared reference or earlier delivery was modified. The only computation here read the two existing saved newest profiles, checked Safe/No11011 across their cyclic wrap, and calculated their run and zero counts; it performed no search, SCC construction or strip expansion.
