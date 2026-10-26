# Exact signed event-height identities, kernel verified

`RootEventHeight.lean` formalizes the algebra in Cedar's `PARITY_HEIGHT.md`, whose read-time snapshot is included. The results apply to arbitrary Boolean drivers a,b,x satisfying

```text
x(t+1) = xor x(t) (a(t) || b(t)).
```

True denotes a black cell. Define Z(t) to indicate a(t)=b(t)=false, and E(t) to indicate a(t)=b(t)=x(t)=false. The integer sign is s(t)=(-1)^t; the white indicator is y(t)=1 when x(t)=false and zero otherwise. The orientation mark is q(t)=s(t)(2y(t)-1). For a Boolean indicator A, H_A(T) is the integer sum of s(t)A(t) for 0<=t<T.

## Verified conclusions

1. For every natural T, with no periodicity or safety premise:

   `2 * (H_Z(T) - 2 * H_E(T)) = q(T) - q(0)`.

   This is the multiplied integer form of the exact telescoping relation. No division or rounding convention occurs.

2. If P is even and x(P)=x(0), then `H_Z(P)=2*H_E(P)`. A second corollary supplies that endpoint return from an all-time period of x. No period assumption for either driver is needed; an even common period is therefore sufficient as a special case. Positivity of P is unnecessary for this identity, and P=0 gives the trivial zero equality.

3. For every T, the correction `H_Z(T)-2*H_E(T)` belongs to `{0,-q(0)}`. These are adjacent integer values because q(0) is either +1 or -1.

4. The event E(t) occurs exactly when x(t)=x(t+1)=false. If x is Safe in the exact all-time sense of having no such consecutive zero pair, then E vanishes and

   `H_Z(T) = 0 or H_Z(T) = -q(0)`

   for every T. With a white initial child, q(0)=+1 and the possible heights are 0 and -1. With a black initial child, q(0)=-1 and the possible heights are 0 and +1. The orientation mark is retained explicitly; the theorem does not require both possible values to be attained.

The local white-indicator identity and event equivalence are checked by ordinary kernel reduction over their eight Boolean input triples. The unbounded temporal statements use algebra and induction, not a bounded temporal experiment.

## Verification and scope

The exact source passed the unchanged official checker at kit pin `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0 and Mathlib 56a005855e. Check.lean SHA256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. All 43 declarations were fully replayed, including definitions and generated declarations; this is not a count of 43 new mathematical theorems. All eight selected headlines passed, with no new axioms. The guarded build and replay took 6.31 seconds and peaked at 1,374,375,936 bytes of owned process-tree RSS. All 300-second/8-GiB-owned/2-GiB-free limits passed.

The only unsuccessful revision had a simplifier-ordering issue in the even-endpoint proof: unfolding the sign definition prematurely prevented the even-sign lemma from firing. The retained final proof rewrites that lemma before unfolding. The statement and checker were unchanged. The failed source and log are retained.

These are local recurrence identities, with no finite-white ancestry premise or conclusion. No converse from unmarked height amplitude, monotonicity through columns, D3* theorem, global completeness, observer conclusion or prize solution is asserted. Cedar's separate ancestry investigations remain separate. No parameter sweeps, GitHub publication or prize submission were performed.
