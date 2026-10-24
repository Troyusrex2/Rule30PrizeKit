# Stripe-related rows cannot first meet late

Research and Lean formalization by OpenAI Codex, working with **Troy Lowry**.

This checkpoint proves a statement for **all finite integer rows, all center
indices, and every finite meeting time**. It does not solve Rule 30 Prize
Problem 1. The missing step is a completeness theorem: equal infinite center
traces have not been shown to force these rows into the stripe relation.

## Statement

Use the moving integer frame

```text
Phi(a) = a XOR ((a << 1) OR (a << 2)).
```

Bit zero is physically on the right. If initial bit `i` represents position
`c-i`, then the center at time `t` is bit `c+t` of `Phi^t(a)`. The exact
local bit identity is proved in `Phi_testBit`.

Read bits from low indices to high indices. A stripe word belongs to

```text
0* (1 | 11) (01)*.
```

Two rows `a,b` are **stripe-related at center index c** if they are equal,
or there is a common cut `j <= c` such that:

1. Both prefixes through bit `j` are stripe words and both have bit `j` black.
2. Both have bit `j+1` white.
3. Every bit above `j+1` agrees between the rows.

The formal definition is `StripeRelated`; the grammar is the inductive
predicate `StripeWord`, not an unproved call to a regular-expression tool.

**Theorem (`stripe_meeting_is_early`).** Let `a,b,c,t` be any natural numbers.
If their center observations agree at every time `s < t`, and their rows at
time `t` are stripe-related at index `c+t`, then they were stripe-related
at time zero or time one.

The two-step theorem `two_step_stripe_related` is the main input: equal center
bits at times zero and one and a stripe relation at time two imply a stripe
relation at time zero or one. Strong induction proves the all-time theorem.

No fixed row width, transient bound, or observation horizon is assumed.
No preservation of the stripe relation under `Phi` is assumed.

**Trace preservation (`stripe_related_same_trace`).** Stripe-related rows
have equal center observations at every time. The key additional theorem,
`stripe_related_preserves_two`, proves that the relation is preserved after
two steps. An elementary bit argument proves equality of the first two
observations, and strong induction proves equality at all times. One-step
preservation is false, as the example below shows.

Consequently, this relation describes a proved source of full trace ambiguity.
Its completeness for equal traces remains open. For pairs with equal entire
center traces, `eventually_stripe_iff_early` proves that entering the relation
at any finite time is equivalent to entering at time zero or one; it does not
assert that such an entry must happen.

## Why the finite certificate proves an unbounded statement

The paired-row transducer streams arbitrary input length, carrying four
previous raw bits per row, the center marker, and three relation parsers for
`a`, `Phi(a)`, and `Phi(Phi(a))`. A balanced tree of **2321 states** certifies
the initial state, closure under every accepted symbol, and absence of the
forbidden final pattern. The certificate is proved with `decide +kernel`.

The finite graph is only one layer. Companion proofs establish:

- Every accepted word of every length remains in the certified state set.
- The packed fields equal the typed stream state and obey their bounds.
- The two streamed output layers are exactly the corresponding integer
  `Phi` bits, including the low-index boundary cases.
- Actual row inputs with the two center equalities are accepted.
- Parser acceptance means identity or an eligible common cut with matching
  higher bits; enough appended zeros turn prefix equality into whole-row
  equality. Five zero input symbols are related to actual rows explicitly.
- The tail parser accepts exactly the stripe grammar above.
- Thus the forbidden final pattern yields the two-step stripe theorem for
  arbitrary integers, and induction yields the all-time first-meeting theorem.

The graph-generation experiment is not trusted as a proof. The unchanged
official checker replays every declaration in each of the twelve modules,
including the certificate and the semantic bridges. The sources use only
the standard Lean axioms allowed by the prize kit.

## Limits and rejected shortcuts

The historical numerical normalization algorithm is in `controls.py`.
Finite comparisons agree with this stripe relation, but their equivalence
has **not been proved in Lean**. Accordingly, the theorem is stated about
the explicitly defined stripe relation.

Normalization is **not equivariant**. For rows `2,3` and center index `1`,
their normalized values at times zero, one, two are respectively
`[2,2]`, `[14,13]`, `[50,50]`. They agree, separate, and agree again. The
proof here allows that behavior and rules out only a first meeting after
time one when the preceding center observations agree.

The following are not proved:

- Every equal infinite center trace eventually becomes stripe-related.
- Equality of the stripe relation with the numerical normalizer's kernel.
- Edge observability, exclusion of every eventual center period, or any full
  prize claim.

This checkpoint is research evidence on GitHub. It has not been submitted
as a new prize essay and has no Wolfram verification status of its own.
The theorem is checked against the official statements' reference environment;
it does not assert the official `Problem1` type.

Recorded validation: all **12 modules, 492 declarations, and 43 selected
headlines** passed the unchanged official checker. Compilation plus full
replay took **337.111 seconds** in total with the kit dependencies already
built. Each module's source hash, timings, and complete checker verdict are
saved in `evidence/`.

The finite controls passed 8191 grammar words, 9000 scalar Rule 30 steps,
28672 exhaustive and 6000 random relation/normalizer comparisons, 8704
two-step trace-guard cases, 822 preservation cases, 5408 preserved trace
observations, and 19160 early-meeting observations. These counts describe
instrument checks; the all-size and all-time statements come from Lean.

## Reproduce

Use Lean 4.35.0 and a prepared official kit checkout at commit
`2f63afda261888e04ec57237290e723190914a1d`. Install Python `psutil` for the
resource guards. The runner verifies the checkout and unchanged `Check.lean`,
then builds and fully replays the twelve modules in dependency order:

```text
python research/normalization-first-meeting/replay.py --project /path/to/pinned-kit --lake /path/to/lake
python research/normalization-first-meeting/controls.py
```

The runner refuses to overwrite a different existing research source unless
`--replace-research-sources` is explicitly supplied after inspection. It
guards every owned job at 8 GiB RSS, 2 GiB minimum system free memory, and
300 seconds; an exceeded guard is a failure, never a proof pass. Full logs
stay in the ignored `evidence/logs/` directory. Sanitized official checker
results and source hashes are in `evidence/`; `manifest.json` records the
exact checked scope and timings.

`generate_certificate.py` reproduces the machine source from the saved
2321-state list. Its Python output does not certify the graph: Lean checks
closure and safety independently of how the list was obtained.

`controls.py` compares the grammar DFA with an independent regex, the integer
update with a scalar Rule 30 truth table, the stripe relation with the older
numerical algorithm, and first-meeting behavior on finite examples. These
controls can expose orientation or off-by-one mistakes. They do not extend
the scope of the formal statements.

## Provenance

The investigation extends the trace-collision experiments in
[`../global-periodicity/`](../global-periodicity/README.md), particularly
`collision-normalization.py`. The first candidate, normalization equivariance,
was falsified by the small example above. The replacement two-step implication
was discovered by finite-state exploration, then all of its row and language
semantics were proved in Lean here. No unchecked external mathematical claim
is a proof premise. No claim of literature priority is made.

The reference checker and official statement come from
[WolframInstitute/Rule30PrizeKit](https://github.com/WolframInstitute/Rule30PrizeKit/tree/2f63afda261888e04ec57237290e723190914a1d).
