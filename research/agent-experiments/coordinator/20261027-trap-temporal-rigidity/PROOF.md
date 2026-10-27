# Proof and quantified scope

Write `F(t,j)` for an actual right-half history, including its prescribed boundary at column zero. The official `IsR30` recurrence is

```text
F(t+1,j+1) = F(t,j) XOR (F(t,j+1) OR F(t,j+2)).
```

No evolution equation is imposed on the prescribed boundary itself. All statements retain the actual recurrence at every updated right-hand column.

## Complete temporal pairs and the strongest conclusion

For arbitrary Boolean time functions, define

```text
predecessor(a,b) = (t |-> a(t+1) XOR (a(t) OR b(t)), a).
s_j = (t |-> F(t,j), t |-> F(t,j+1)).
```

The actual recurrence gives `predecessor(s_(j+1)) = s_j`. No temporal periodicity is needed for this identity. If `s_i = s_j` for `i < j`, the existing generic `inverse_collision` theorem yields a positive return of `s_0` under `predecessor`.

The normalized trap head is the pair of 21-periodic functions encoded by `(1198372,1591590)`, where bit `t` gives the value at time `t`. The new `decode21_step` theorem proves that decoding the existing numeric predecessor agrees exactly with applying the function predecessor. `decode21_injective` proves that bounded encodings are recovered uniquely. Therefore the existing numeric `head_no_return` theorem implies `decoded_head_no_return`: this complete head pair has no positive return under the function predecessor.

Consequently `normalized_pairs_ne` excludes equality of the complete temporal traces of any two spatial pairs in an actual history with that normalized head. Only the two head functions are prescribed periodic profiles. There is no period assumption on the remaining columns.

For any actual aligned `t001` entry and any time bound `B`, the official trap invariant supplies a later time `b >= B` at which the boundary and first updated column have the normalized head traces for all subsequent times. This is `trapped_normalized_after`; it uses the invariant's label progression and the verified full head projection, including black driver phases. If two spatial pairs agreed at every time after `B`, their complete traces after `b` would agree, contradicting `normalized_pairs_ne`.

Thus `Rule30TrapPeriod21.trapped_pairs_differ_arbitrarily_late` states, for every `j < k` and every `B`,

```text
exists t >= B,
  (F(t,j),F(t,j+1)) != (F(t,k),F(t,k+1)).
```

The entry assumptions are: `T <= t1`, boundary `F(t,0)=wordAt3 t001.w (t-T)` for all `t >= T`, an index `i < t001.n`, phase equality `(t1-T)%3 = t001.lab i%3`, and the actual finite-prefix encoding `EncF F t001.b t1 0 (t001.st i)`. Finite support is not assumed. The theorem neither says that every individual column trace is different nor that the pairs disagree at all late times.

## Reused finite certificate

For a 21-bit profile let `U a(t)=a(t+1 mod 21)`. The numeric predecessor is

```text
step(a,b) = ((U a XOR (a OR b)) mod 2^21, a).
```

The earlier, unchanged certificate proves a 1967-step path from the normalized head pair to a closed 26313-step cycle avoiding that head. Its 206 checked segments have length at most 128; a generic safe-path composition theorem joins them. The kernel checks endpoints and exclusion at every required position. The argument needs neither a least preperiod nor a least cycle length, and proves neither as part of this claim. It does not enumerate the full `2^42` state space.

A point that reaches a closed cycle excluding itself cannot have a positive return: a sufficiently large multiple of a putative return time would lie on that cycle and equal the forbidden point. This is the unchanged source of `head_no_return`. The existing family also verifies the complete head projection against all 815 official trap states and the 21 bits of the driver profile. The strengthened proofs reuse those results; they do not substitute a free-boundary strip for an actual full right-half history.

## Generic common-period rigidity

Suppose an infinite inverse chain satisfies `f(s_(n+1))=s_n` and all its states have injective codes of one fixed finite bit length. Pigeonhole gives a positive return of every suffix head `s_n`. If its return time is `q > 0`, then `f^n(s_n)=s_0` and

```text
f^((q-1)n)(s_0) = f^(qn)(s_n) = s_n.
```

Every chain state is therefore in the forward orbit of its head. Any property preserved by `f` propagates from the head to the whole inverse chain. Equivalently, a map commuting with `f` and fixing the head fixes every chain state. The generic results impose finite coding on the chain, not finiteness of the ambient type or injectivity of `f`.

If an actual right-half history has a positive common temporal period `p`, each pair of complete profiles has an injective code of length `2p`. The function predecessor preserves any specified temporal period `r`. If columns zero and one are `r`-periodic, the generic argument makes every column `r`-periodic. The theorem is `Rule30PeriodicHalfline.common_period_head_rigidity`. No divisibility relation between `p` and `r` is required; `p` need not be a least period.

## Different column onsets

Suppose `p > 0` is fixed and for every column `i` there is an onset `T_i` with

```text
F(t+p,i)=F(t,i) for every t >= T_i.
```

There is no common bound on the `T_i`. Choose one onset for each column and define

```text
G(t,i)=F(t+T_i*p,i).
```

Each shift is a multiple of the same `p`, so absolute time residues are preserved. `G` is globally `p`-periodic and agrees eventually with `F` in each column. To verify one Rule30 stencil, align its three columns at a sufficiently late common multiple of `p`; only those three onsets are needed. This proves `IsR30 G`. Every finite spatial prefix has a common late agreement time, although no such time is asserted for the whole half-line. This construction is `exists_periodic_representative` and its supporting lemmas.

An eventual head period `r` transfers to `G`; global `p`-periodicity moves any time into its late agreement range and makes that head symmetry exact. Common-period head rigidity then propagates `r` through `G`, and columnwise late agreement transfers it back to `F`. This is `eventual_common_period_head_rigidity`.

For a trapped history the head has eventual period 21. Any proposed positive common eventual period `p` would therefore make every column eventually 21-periodic. The periodic representative agrees with the actual history on the finite trap strip at a late invariant entry, so the original period-21 obstruction applies. This proves `no_common_eventual_period_trapped`, with the same boundary and entry assumptions as the pair theorem and the additional proposed clock

```text
p > 0 and forall j, exists S_j, forall t >= S_j, F(t+p,j)=F(t,j).
```

## What remains open

Neither trap entry from arbitrary finite right rows nor `AbsorptionT t001` is proved. The results allow unbounded individual eventual column periods and aperiodic exterior columns. They do not identify the right half of the single-seed Rule30 orbit with a trapped history under an unproved boundary hypothesis. Rule30 Problem 1 remains open in this contribution.

The integration preserves the previous profile and certificate bytes and the original family proof bodies. The generic and new family proofs were previously checked as separate research sources and then mechanically moved to the canonical namespaces. The final canonical twelve-source replay is separate evidence: 814 contribution constants and 32 headline types passed with no new axioms. The actual targeted Lake build and named-head checker invocation also passed. See the README for reproduction and the separate portable receipts.

Contributed by Troy Lowry with OpenAI Codex, reusing the credited official definitions, trap certificate and invariant, and core pigeonhole theorem.
