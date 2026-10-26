# Even-clock rigidity for a plateau observation

This is a uniform local theorem, not a solution of Rule 30 Prize Problem 1.
For every actual triangular Rule 30 history `a`, every `j`, and every even
clock `P = 2*n`, suppose `h(t) = a(t,j+3)` flips after P steps and
`k(t) = a(t,j+2)` repeats after P steps. Then, writing `g(t) = a(t,j+4)`,
**the trace `g OR h` does not repeat after P steps**. No period assumption
on g is required. No assumption of finite initial support is required.
The actual-history recurrence supplies the two older profiles used below.

The headline is
`Rule30EvenModeRigidityResearch.actual_even_plateau_or_clock_rigidity`.
The complete source SHA-256 is
`38e74acb17c0ddc2b40dc92e49052cb567056621bb8b18e8e28e16983f4b452b`.

## Proof

First assume g repeats after 2P steps. Set `q = delta_P g`,
`rho = delta_P (g OR h)`, and `S = NOT delta_1 rho`, where delta is XOR
of the shifted and original traces. The previously checked clock-mode
identities give `q' = q XOR NOT k`, `q(t+P)=q(t)`, and
`S = q OR (NOT k AND NOT l)`, with l immediately older than k.

If S were constantly one, its values at t and t+1, together with
`k' = k XOR (l OR m)`, force `k OR l = k`. Therefore
`h' = h XOR k`, and `z = h XOR q` flips at every step. An even number P
of flips returns z to itself. But h flips and q repeats after P steps,
so z must flip after P steps. This contradiction proves the constant-mode
exclusion uniformly for all even P.

Now suppose `g OR h` repeats after P steps. Since h flips after P steps,
the OR trace must be constantly one. A prior clock-shift identity supplies
a constant Boolean flag e with `g(t+2P) = g(t) XOR e`. There is a time
with h=0, and h is also zero 2P steps later; the saturated OR trace forces
g=1 at both times. Hence e=0, giving the missing 2P period of g. Its
constant OR trace makes S constantly one, contradicting the first part.

The relevant lemmas are `constant_readout_driver`,
`even_constant_mode_impossible`, `constant_or_forces_double_period`, and
the headline above. Every recurrence and clock premise is explicit in
the checked theorem statements.

## Verification and controls

The new module builds and passes the unchanged official checker at
kit commit `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0.
All **17 declarations**, with six selected headlines, were kernel replayed;
there are no new axioms. The final guarded build and replay took 1.739 s,
with peak owned RSS 778,952,704 bytes on G913. The checker SHA-256 is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
This is local full replay, not a Wolfram backend or human review verdict.

Independent Python controls use the literal Rule 30 truth table and
exhaust all five-cell cyclic walks in the stated relaxation at clocks
1, 2, 3, and 4. Both even clocks have no qualifying constant-mode or
saturated-OR walk. The odd clocks have witnesses: the parity premise is
essential. The support gate passes its complete truth table; removing
either of its two observation premises admits a counterexample. These
finite controls supplement, rather than prove, the uniform Lean result.

## External result audited

[PR30](https://github.com/WolframInstitute/Rule30PrizeKit/pull/30), by
**Elijah08-GIT with OpenAI Codex**, adds coupled-history right-germ
constraints. Its exact head is `de833dae04e9bb5e6e7e62add7b304a70f6532a7`;
`Rule30CoupledGerms.lean` SHA-256 is
`19eb466ca6dc36f0df1a51ad802f61f7a11aee4c32fd256f11b55817dc93090d`.
We fetched the exact Git object and locally replayed all **33 declarations**
and seven headlines against the same unchanged checker. This is their
work, not a new result of this checkpoint.

Its zero-germ transport proves an exact right-root relation after a late
black anchor when a no-11 driver has zero germ at late falling transitions.
For periodic drivers, cofinal black cells, literal coupling, and a finite
configuration (or an occupied left edge), Jen's theorem then forces
nonzero germs at cofinally late falling transitions. It does not settle
the unresolved coupled-history or prize statement. PR29's period-32
shielding proposal was read for scope only; its proofs were not adopted.

## Experiments discarded

The proposed quadratic decoder of q(0) from arbitrary samples of S fails
already at clock 32, and again at clock 64. Saved dual witnesses contain
192 and 960 actual cyclic rows. An independent script recomputes every
row with literal Rule 30, audits 12,369,920 cell updates, and checks that
every degree-at-most-two observation monomial has XOR zero while q(0)
has XOR one. This rules out only that polynomial template at those clocks.
It does not refute an unrestricted observer. These witnesses are Python
audited; no Lean theorem for these quadratic witnesses is claimed.

The same-clock representation search also fails to represent S, rho, or
the suggested OR variants in most tested prefix graphs. This is only
nonmembership in the chosen same-clock graph, not a proof of general
nonrealizability with larger-clock ancestors or subsequent period drops.

## Remaining gaps

The lower-clock mode observer is still unproved. The experiment that
motivated it additionally requires every prefix ancestor to be P-periodic;
that condition cannot be inferred merely from k being P-periodic.
Longer plateau chains and possible period drops remain unresolved.
The full penultimate-bit observer, invariant reader sink separation,
and the bridge from a fixed sheared depth to the physical center column
also remain open. This theorem removes one constant-observation escape;
it does not close those gaps or justify saying we are near the prize.

No new prize submission or pull request accompanies this research archive.
The earlier 2,963 selected hashes across 35 archives were checked unchanged.
See [REPRODUCE.md](REPRODUCE.md) and [BRIEF.md](BRIEF.md).
