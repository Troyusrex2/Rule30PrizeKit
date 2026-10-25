# Round two: new ideas after testing all seven responses

Prepared for Troy Lowry's seven independent agent sessions, 25 October 2026.
**Problem 1, Q01 and CQ01 remain open. We have no full solution or reliable
estimate of how close one is.** This is an update to the original handoff,
not a request to repeat it.

Start with this brief, pick your corresponding question in [TASKS.md](TASKS.md),
and return several independently classified findings if useful. The tasks are
starting points: a different mechanism with a precise test is welcome. The
[copyable prompts](prompts/) refer to each of the seven original response IDs.

## Objective, conventions and verification

The target is the official
`Ruliology.CellularAutomata.Rule30Prize.Problem1`: the center column from a
single black cell is not eventually periodic. The rule is
`new = left XOR (center OR right)`. Fix coordinates, boundary conditions,
packing direction and time conventions before comparing experiments.

Use research base **`102d5b8e938b031a6d4df53541d9da2c50ffb859`** from
Troyusrex2/Rule30PrizeKit, branch `research/unbounded-sparse-20261024`.
This is distinct from the verifier reference:

- Kit/checker pin: `3eca23c0a9fa6b153313655e6d51835406c2d06e`.
- Lean: **4.35.0**.
- Unchanged `Check.lean` SHA-256:
  `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

The checked results below passed local rebuild and full replay of every owned
declaration, including theorem and axiom checks. They are not new Wolfram
review verdicts. Read exact theorem types and include all custom dependencies.
Do not use `sorry`, new axioms, `native_decide`, `bv_decide`, a modified checker
or skipped declarations. Experimental ideas are welcome; label them honestly.

The [original handoff](../../README.md) supplies definitions and tracks A-H.
CQ01 is the coupled period-two sufficient route, not the full prize theorem.
The official sideways reduction expresses it as infinite support of `Psi R`
for each finite right half `R`. Even a proof of CQ01 leaves other periods to
handle. Do not turn a result about an arbitrary driver into a result about
the actual coupled driver, or infer an infinite assertion from a long trace.

## New checked facts that change the search

### A generic obstruction to absorbing-prefix ranks

Read [the generic barrier](../20261024-seven/GENERIC-ABSORBING-PREFIX-BARRIER.md)
and its [integer-geometric proof](../20261024-seven/INTEGER-GEOMETRIC-FINITE-IMAGE-BARRIER.md).
The headline is
`Rule30GenericAbsorbingPrefixBarrierResearch.no_absorbing_prefix_geometric_rank`.

For **any** transition function `T : Nat -> Bool -> Nat`, if its reader reaches
a permanently absorbing state after the specified 26-cell common ether prefix,
no proposed signed integer prefix energy of the following form meets all the
stated rank and lower-bound conditions, for any integer `lambda >= 1`:

```
E_r(w) = H_r + sum_i lambda^i * C_r(state before w[i], w[i]).
```

The lower-bound domain retains canonical finite words, actual finite
predecessors with black head and preceding free bit one, and thirteen forward
double-step conditions (black even head, alternating odd stream). Exact full
physical witnesses have lengths 34, 36 and 38. The theorem contradicts a
strict drop on the first specified double step and nonincrease on the next.
It allows signed costs, arbitrary integer phase offsets and an additive lower
bound; it does not assume each letter cost is nonnegative.

Two infinite families of actual finite images yield pump inequalities. Their
complete moving-front suffixes are retained; the geometric cone identity is
uniform in the integer scale. This removes the earlier defect where the
starting witness had no finite predecessor. Counts: 200 replayed declarations
for the unit-scale finite-image release, 126 for its integer-scale extension,
and 21 for the generic-reader extension. Counts include generated declarations
and are not counts of independent mathematical discoveries.

**Escape routes remain:** a reader that keeps recognizing the period-seven
background, resynchronization, costs using the full right half, noninteger
scales, longer actual-past restrictions, different lower-bound domains,
nonlinear or nonlocal resources. The theorem does not exclude all readers or
all finite-state proof methods. State explicitly why your proposal falls
outside its hypotheses, or try extending the obstruction rather than fitting
inside an already excluded class.

### A coefficient-one charge is false, including every additive allowance

The target under investigation was

```
5*zeros(free R,n) <= n + B + C*blackCount(Psi R,2*n+1).
```

The [checked finite-right witness](../20261024-seven/CRITICAL-CHARGE-ONE.md)
has actual free stream `01` repeated and sideways positive-depth row
`1100001` repeated. At every `n=14*k`, its zero count is `7*k` and its
sideways black count is `12*k`. Thus **C=1 fails for every B**. This uses an
official ether-trap invariant, not just a simulated prefix. Core and bridge
passed 104 declaration replays. Natural C must be at least two for this
witness; **C=2 sufficiency is unproved**. Variable coefficients, scale charges
and the separate No00 spatial-charge question remain open.

### A defect clock gives a weaker sufficient target

Read [QUANTITATIVE-DRIFT.md](../20261024-seven/QUANTITATIVE-DRIFT.md).
For a hypothetical finite left row in `InX`, with last black depth `m` and
Golden odd stream `s` (neither `00` nor `11111`), the checked identities give

```
5*zeros(s,n) + trailing(s,n) = n + D(s,n),  trailing <= 4,
D(s,2*N+m+16) >= D(s,N)+1,
cutoff(m,k) = (m+16)*(2^k-1),
D(s,cutoff(m,k)) >= k.
```

This is logarithmic-scale growth, **not a positive density gap** above 1/5.
An open sufficient bound, with `n=cutoff(m,k)`, is

```
forall finite R, forall m, exists C B, forall k,
  5*zeros(free R,n)
    <= n+B+C*blackCount(Psi R,2*n+1)+floor(k/2).
```

`Rule30GoldenScaleChargeResearch.CQ01_of_scale_charges` proves this would imply
CQ01. Constants can depend on both R and m. Changing that quantifier order
changes the problem. The missing inequality is not established.

## What happened to the original seven ideas

See the [first experiment report](../20261024-seven/REPORT.md) for exact
commands, counterexamples and limitations. Every original response was tried.

| Original session | Test outcome | Useful next change |
|---|---|---|
| CoinAIlyzer backend | Generic four-width reader refuted by a kernel-checked same-width collision. Larger learned readers supplied no new discriminator. | Preserve relevant background or seed ancestry; prove a horizon or a new invariant. |
| photograde | High scores collapse to chance after low-grammar and matched-top controls. | Test a mechanism using actual coupling against hard matched controls; extract its meaning. |
| codex-sanity | Zero survivors among 100,000 exact sampled matrix assignments. Not exhaustive over all matrices. | Derive an identity, determinant or rank-growth mechanism. |
| codex-cedar | Local disagreement identity checked; two paths can cancel, already at seed time three for the tested comparison. | Prove an odd residual after cancellation using actual ancestry. |
| swarm, run 214719Z | Moving-edge asymmetry reproduces; it does not prove fixed-column periodic inheritance. | Derive a valid relation using both neighbors and the actual seed. |
| swarm, run 214738Z | Million-step catalogs keep growing; arbitrary-exterior closure fills all words at tested widths. | Seek an unbounded normal form or restricted reachability mechanism. |
| wiki | Entropy matches generic local-rule constraints; the tested spectral threshold accepts every candidate period word. | Obtain a seed-specific reachability or charging estimate. |

An additional **unrestricted** unit zero-run charge is kernel-refuted at n=28.
That example has adjacent free zeros; it does not refute the No00-restricted
claim. Do not conflate this with the separate actual-finite-R C=1 failure above.
Ordinary strip, finite-state, matrix, entropy, neural or PSD failures exclude
only their stated families, not all approaches using those tools.

## Latest combined-reader searches: no positive certificate

The new [experiment record](EXPERIMENTS.md) and exact [evidence](evidence/)
combine a correctly aligned **1,110-state multi-background reader**, actual
finite history of depths 2-4, upcoming-free-bit phases of width 2/4, a
thirteen-double-step future guard and complete moving fronts. This reader
retains the period-seven background and escapes the absorption hypothesis.

Two unit-scale cases return optimum rate zero. The depth-four unit-scale
positive-rate retry is reported infeasible by the native solver. Both scale-two
retries time out at 600 seconds with no incumbent; the 3/2-scale case has a
native numerical error. **These are finite model outcomes, not Lean
impossibility proofs.** All cases are finished; none is still running.
Independent physical, language, reader and exact rational energy controls
passed. There is no new candidate rank to formalize.

Avoid spending another large budget on the identical models without a reason.
Useful alternatives include exact dual witnesses, proof-derived redundant
cycle cuts, changed semantics, or a mechanism outside additive prefix scores.
Describe any change to the modeled proposition separately from a solver change.

## What to send back

Aim for two or three independent findings: a concrete proposal, its quickest
serious falsification, and a precise missing lemma or surviving mechanism.
Mixed outcomes are expected; a reproducible failed idea is useful. Prefer a
qualitatively new argument over another width, tail or finite catalog entry.
Check the public submissions and kit catalog before investing heavily. Only
use independently checked source as a proof dependency; a verified tag or
abstract alone is not our replay of that source.

Use [the existing response format](../../RESPONSE_FORMAT.md), the round-two
[manifest template](manifest.template.json) and [report template](REPORT.template.md).
Keep campaign ID `rule30-20261024`; put your R2 task label in the report/title,
not in new schema fields. Findings are `F001`, `F002`, etc., each with its own
status and evidence. Cross references use `<response_id>#F001`.

- Local delivery: `D:\MWB\Rule30\agent-inbox\<response_id>\`.
- Remote delivery: PR to Troyusrex2/Rule30PrizeKit, base
  `research/unbounded-sparse-20261024`, adding
  `research/agent-experiments/responses/<response_id>/`.
- Write `READY` **last**, after source, evidence, hashes and manifest.
- Fresh run: fresh timestamp/nonce ID. Revision: new versioned directory plus
  `supersedes`; leave originals intact. Multiple responses per agent are fine.
- Work in a separate clone/worktree with independent build output. Never edit
  another agent's folder, the coordinator's index or the shared reference build.
- State limits, failed checks, actual solver status and resource bounds.
  Timeout/error is unknown; a process exit code of zero is not a certificate.
- No credentials, machine configuration, authentication output or unrelated
  private files. Do not submit a new prize essay as Troy; return it for review.

No agent has been contacted by this file. Troy can forward a matching prompt
to each existing session. The response directories handle simultaneous replies.
