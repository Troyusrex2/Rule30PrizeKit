# A2 anti-period signed-height obstruction, kernel verified

`RootAntiPeriodHeight.lean` proves the uniform necessary condition in Cedar's adversarial report A2. It imports the unchanged `RootEventHeight` source from its immutable delivery. The read-time Cedar report is retained for provenance; only A2 is formalized here, not the other claims or constructions in that report.

Let P be positive and even. Let b and c be arbitrary Boolean histories with

```text
b(t+P)=b(t),       c(t+P)=!c(t).
```

Let d satisfy the exact recurrence `d(t+1)=xor d(t) (b(t)||c(t))` and be Safe at every natural time, meaning it never has two successive false values. No recurrence for b or c, older periodic ancestor, finite-white origin, or supplied child clock is assumed.

For v(t)=!b(t), write H_v(T)=sum_{0<=t<T} (-1)^t bit(v(t)). The main theorem `anti_period_safe_necessary` proves

```text
H_v(P)=0,
and for all S,T : Nat,  -2 <= H_v(T)-H_v(S) <= 2.
```

The difference statement is the precise amplitude-at-most-two condition, including arbitrary time horizons rather than only one enumerated cycle. A direct corollary proves that nonzero period drift or any height increase greater than two rules out Safe d. Since S and T are arbitrary, reversing their order also covers a decrease below minus two. Neither theorem asserts a converse.

## Exact proof route

Set Z(t)=[b(t)=c(t)=false]. Pointwise anti-periodicity gives the integer identity

```text
bit Z(t) + bit Z(t+P) = bit (!b(t)).
```

Because P is even, shifting by P preserves the temporal sign. Induction on T proves the paired-height identity with its required offset:

```text
H_v(T) = H_Z(T) + H_Z(T+P) - H_Z(P).
```

The verified marked safety theorem places every H_Z(T) in the same oriented pair `{0,-q_d(0)}`. Consequently any difference of two Z heights lies between -1 and 1. Subtracting the paired identities at T and S gives the sum of two such differences, establishing the bound two.

For any even-periodic Boolean mask A, a separate finite-sum induction proves `H_A(T+P)=H_A(T)+H_A(P)`, and hence `H_A(3P)=3H_A(P)`. Apply the difference bound between zero and 3P. The drift H_v(P) is an integer, so `-2 <= 3H_v(P) <= 2` forces H_v(P)=0. No limit argument, mask cardinality approximation, phase quotient, or unmarked-height safety criterion is used.

The auxiliary lemmas do not need positivity of P; the main A2 statement explicitly retains the requested positive-even hypothesis. They remain exact at P=0, although an anti-zero Boolean history cannot exist.

## Verification

Both sources were freshly compiled and fully replayed with unchanged `Check.lean`, at kit pin `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0 and Mathlib 56a005855e. The checker SHA256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

- RootEventHeight dependency: 43 declarations, unchanged source SHA256 `c3e092489185d6f38bf3313c027776b90e66b1485c431c2ab9e1ee33ed8248b4`.
- RootAntiPeriodHeight: 26 declarations, including generated declarations, with all six selected headlines passing. There are eleven named lemmas in the source; 26 is not a count of new mathematical theorems.
- The new module passed on its first build. Its guarded build and replay took 6.20 seconds and peaked at 1,374,752,768 bytes of owned process-tree RSS.
- All 300-second, 8-GiB-owned and 2-GiB-free resource guards passed. No new axioms, native decisions or checker changes were used.

This is a uniform necessary-condition theorem for arbitrary drivers with the stated periodicity. It does not establish finite-white ancestry, D3*, global completeness, monotone obstruction propagation, an observer conclusion, or a prize solution. No certificate cases, parameter sweeps, GitHub publication or prize submission were added. The previous RootEventHeight delivery remains immutable.
