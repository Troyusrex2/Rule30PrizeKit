# Rule 30 research handoff for independent agents

Prepared for Troy Lowry and his agents, 2026-10-24. **Prize Problem 1 remains
open in this work. We do not have a near-complete proof.** The aim is a full
Lean proof or disproof of the official statement, with useful failed
experiments retained along the way. Bring existing advances; you do not need
to restart your work around our preferred approach.

## Start and return a response

**Latest experiments:** [global credit, source-aware gaps and renewal clocks](coordinator/20261025-global-credit-tests/REPORT.md). Fitted ranks fail exact held-out checks; solver timeouts and unresolved global classes are kept distinct. No new theorem or prize solution is claimed.

**Upstream contribution:** [PR21](https://github.com/WolframInstitute/Rule30PrizeKit/pull/21) contains the uniform conservation proof as a core catalog module. [Build, full replay and scope](coordinator/20261025-conservation-catalog/REPORT.md). Open for review; absent from the current reference kit.

**Latest checked experiment:** [a strict cycle rules out one causal block-rank template](coordinator/20261025-causal-block-cycle/REPORT.md), including ordinal-valued ranks. Larger contexts and cross-block credit remain open.

**Previous checked additions:** [uniform conservation classification and exact ancestry frontier](coordinator/20261025-greedy-and-conservation/REPORT.md).
The report includes all-width kernel proofs and separately labeled inverse-design experiments; the decisive growth and coupling premises remain open.

**Previous review:** [all seven round-two responses have been reviewed](coordinator/20261025-round2-review/REPORT.md).
The review includes a new all-time, kernel-checked coefficient-two charge
counterexample, checked ancestry and defect-transfer tools, independent
reproductions and explicit failed density extrapolations. Problem 1 remains open.

The [round-two brief](coordinator/20261025-round2/BRIEF.md)
summarizes the new checked barriers, counterexamples and completed experiments.
It includes [seven different follow-up tasks](coordinator/20261025-round2/TASKS.md),
[copyable prompts for the original sessions](coordinator/20261025-round2/prompts/),
updated templates and the latest source/results archive. Multiple findings and
simultaneous responses still use the existing append-only intake format.

The [critical-drift and uniform-reader followup](coordinator/20261024-seven/UNIFORM-READERS.md)
proves that bounded excess above the minimum Golden zero density forces
eventual period five, giving a weaker sufficient counting target for CQ01.
It also records the complete numerical search over 65,536 two-state readers
and the unsuccessful drift searches. The counting target remains unproved.
Use its [corrected byte manifest](coordinator/20261024-seven/UNIFORM-READERS-CORRECTION.md)
when auditing the archived worker checkpoints.

The [memory and new counting-target report](coordinator/20261024-seven/MEMORY-AND-NEW-TARGET.md)
records the larger worker's full kernel checks, a partitioned budget-eight
certificate, and a weaker open target counting both odd and even spatial
coordinates. It includes an exact obstruction to a restricted count rank
and new reader, stack and spatial-flux failures. The new counting premises
remain unproved; this is not a near-complete prize solution.

The [coupled-language and counting report](coordinator/20261024-seven/COUPLED-LANGUAGE.md)
adds two kernel-checked forbidden words, a checked population certificate,
and a proved reduction of CQ01 to an explicitly open counting inequality.
It also preserves the finite language censuses, failed ranking searches and
inconclusive longer solver queries. It is not a prize solution.
The [further tests](coordinator/20261024-seven/FURTHER-TESTS.md) add a complete
sparse budget-14 census, stronger bounded SAT checks, extremal examples and
failed neural/quadratic ranks. The unbounded counting inequality remains open.

The [reviewed catalog integration](coordinator/20261024-seven/REVIEWED-CATALOG.md)
is now in [PR #16](https://github.com/WolframInstitute/Rule30PrizeKit/pull/16):
the consolidated method and its tail-13 use pass all 326 declaration replays;
the older PR #15 is superseded. The record includes the exact sources and
same-machine build comparison. Upstream verification and merge are pending.

The [coordinator report](coordinator/20261024-seven/REPORT.md) records attempts
on all seven original responses. Later work includes the
[checked parallel return-map method](coordinator/20261024-seven/COMPRESSED.md),
[general catalog tools and PR #16](coordinator/20261024-seven/FRONT-TOOLS.md),
and [new contribution audits and further falsification experiments](coordinator/20261024-seven/SECOND-PHASE.md).
The [prescribed-even-coordinate route](coordinator/20261024-seven/EVEN-SUPPORT.md)
adds a checked decoder/language guard and a result allowing unrestricted odd
spatial tails. Its uniform support-size premise remains open.
Problem 1 and the general support questions remain open.

Read this handoff, choose a sharply stated experiment, and try the quickest
serious falsification before a large search or formalization. Different
representations and unexpected counterexamples are welcome. A negative result
with a reproducible reason is a useful response.

**Use [the response format](RESPONSE_FORMAT.md).** Every response has a unique
directory and can contain multiple independently classified findings.
Multiple agents, multiple runs, revisions, and conflicting findings coexist;
there is no shared response file to overwrite.

- **Remote agents:** open a PR to **Troyusrex2/Rule30PrizeKit**, base branch
  **`research/unbounded-sparse-20261024`**, adding your response under
  **`research/agent-experiments/responses/<response_id>/`**. Use your own
  fork/branch. Send Troy the PR link. These are intake PRs to Troy's fork,
  not mathematical-contribution PRs to the official kit.
- **Agents on Troy's machine:** put the same response directory under
  **`D:\MWB\Rule30\agent-inbox\<response_id>\`**. Write the `READY` marker last.
- **If neither destination is accessible:** give Troy the complete response
  folder or archive, with its response ID. Keep the manifest and report intact.

Do not edit another agent's folder, the coordinator's index, this checkout,
or the shared reference project's build artifacts. Use a separate clone or
worktree with its own build output. There is no need to ask permission to
return a failed experiment. Do not submit a new prize essay under Troy's
Wolfram identity: return it for review and explicit submission approval.

## Exact objective and environment

The rule is `new = left XOR (center OR right)`. The initial row is a single
black cell at position zero. The official goal is

```lean
Ruliology.CellularAutomata.Rule30Prize.Problem1
```

It says that `center(t) = cell(t,0)` is not eventually periodic. A full proof
must cover every onset and every positive period, not only period two or a
finite observation window. A valid counterexample must establish an infinite
eventual period for this exact seed, not a different configuration.

The research-code baseline for this handoff is
[`54e9a19e078fc84a7b488d1748a851d5e1bd6d64`](https://github.com/Troyusrex2/Rule30PrizeKit/tree/54e9a19e078fc84a7b488d1748a851d5e1bd6d64).
The official verifier pin checked while preparing this handoff is
[`3eca23c0a9fa6b153313655e6d51835406c2d06e`](https://github.com/WolframInstitute/Rule30PrizeKit/tree/3eca23c0a9fa6b153313655e6d51835406c2d06e),
Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and
LeanLink 1.2.1. The research branch is **not** a replacement for that verifier
checkout. Use a separate official reference checkout to validate proofs.

Before relying on new public work, refresh the
[environment](https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/environment),
[submissions](https://www.wolframcloud.com/obj/rule-30-prize/Agents/submissions.json),
[agent instructions](https://www.wolframcloud.com/obj/rule-30-prize/Agents/skill.md),
and the kit's `lean/README.md` and `equivalents/CATALOG.md`. Match the checker
pin to the one you actually used. New source must be independently checked
before becoming a premise; a public status label or successful compilation
alone is not our verification standard.

## Verified results worth using

### Canonical comparison and the seed's boundary class

Use the moving integer frame

```text
Phi(a) = a XOR ((a << 1) OR (a << 2)).
```

Bit zero is physically on the right. At center index `c`, the observation at
time `u` is `Phi^u(a)[c+u]`. An eventual seed period with onset `T` and period
`P>0` would give equal entire traces for exactly these aligned rows:

```text
a = Phi^T(1) << P
b = Phi^(T+P)(1)
c = T+P.
```

Row `a` is positive and even. Row `b` has `SeedLow`: bit zero is black, and
bits one and two are equal. It also has a black bit strictly beyond all
black bits of `a`. These statements and the bridge to the exact official
Problem 1 are proved in
[Rule30SeedBoundaryResearch.lean](../trace-completeness/Rule30SeedBoundaryResearch.lean).
The proposed sufficient condition `SeedLowEvenLeftSeparation` is **open**.
Proving separation just for the canonical pairs above is enough; a theorem
for all even/seed-low pairs is a stronger target and might be false.

### A proved source of entire-trace ambiguity

In the adopted
[`Rule30StripeMeeting`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/3eca23c0a9fa6b153313655e6d51835406c2d06e/lean/Ruliology/CellularAutomata/Rule30StripeMeeting.lean)
module, stripe-related finite rows have equal observations at every time.
The eligible low-bit words, read low to high, have grammar `0* (1|11) (01)*`,
a common black cut, a common white separator, and identical higher bits.

We proved that a pair with the preceding observations equal cannot first
enter this relation after time one. We also proved that canonical seed
period pairs can never enter it. **Completeness is open:** equal infinite
traces have not been shown to imply this relation. Full-row recovery is
false. Edge recovery and the seed-specific separation target remain open.
See [the semantic proof and scope](../normalization-first-meeting/README.md)
and [the trace investigation](../trace-completeness/README.md).

### Exact reconstruction and the period-two support question

Quint and Gemini's
[all-depth reconstruction](../catalog-review/README.md#all-depth-period-two-reconstruction-audit)
was independently replayed from its exact source: 139 declarations and 17
selected headlines at the current pin. Its `skelPair(s,m,k)` reconstructs
all left columns from the free sequence under a normalized alternating
center. Arbitrary free sequences also have exact zero-boundary realizations.

Our [decoder](../even-depth-decoder/README.md) proves that the initial even
spatial cells determine a unique free sequence and a unique odd spatial row.
Write `F(u)=oddCode(u)` for that odd row. `FiniteBits` means eventually all
white. We proved the exact equivalence

```text
Rule30PeriodTwo.Q01
  iff for every u, FiniteBits(u) implies not FiniteBits(F(u)).
```

Both sides remain **open**. We also proved the exact next-odd-cell sensitivity:
flipping free bit `d` changes `Theta(s)[2*d+3]` by the parity of a preceding
anti-diagonal. That coefficient can be zero. An assumed unit pivot for odd
cells is invalid. The decoder and sensitivity modules have 72 declarations
and 13 headlines with full kernel replay; their report also includes the
fresh external reconstruction replay.

For an **actual coupled alternating center**, the free sequence has no `00`
and no `11111`, proved in official
`Rule30ZeroBoundary.free_bits_no00_no11111`. Arbitrary zero-boundary
reconstructions do not inherit those restrictions. Finite full starts in
`InX` would also have non-eventually-periodic free bits, by the existing
`free_not_eventuallyPeriodic` theorem. Periodic-freebit experiments therefore
do not resolve the difficult unrestricted case.

### Controlled response and the finite right half

Known terminal rewrites preserve right-half responses, but their completeness
has not been proved. Our [response-growth theorem](../response-growth/README.md)
shows that high caps `100/111` remain irreducible under those rewrites and
grow by one bit at every step, for every prescribed driver. A constant driver
can even produce a constant head output while the irreducible state grows
without bound. A bounded-normalizer argument needs a new, justified premise.

The [external semigroup audit](../catalog-review/README.md#semigroup-and-coupled-reduction-submission-audit)
has 653 fully replayed declarations. It supplies useful coupled and absorption
interfaces. Its global absorption hypotheses remain open. Empty-right-half
results do not cover arbitrary finite right halves. White-tail erosion does
not by itself establish the required trap absorption.

## Independent experiment tracks

Choose one or several. Return separate findings when claims or evidence differ.
These are research questions, not accepted premises.

| Track | Question | A useful response |
|---|---|---|
| A — Canonical seed separation | Use that both aligned rows come from the **same seed orbit**, with a specific time lag. Can they share an entire trace? | An unbounded proof, a genuinely new invariant using this coupling, or an exact counterexample to a stronger proposed condition. |
| B — Odd support and parity | Can finite even input and the exact sensitivity formula force arbitrarily distant odd black cells? Alternatively, does no `00` in the free sequence already force infinite odd support? | A support-growth mechanism or a certified infinite counterexample. Distinguish unrestricted Q01 from the extra restrictions of actual coupling. |
| C — Trace holonomy and ancestry | With the right prefix supplied, inverse trace reconstruction is proved. What does changing that prefix do to eventual zero tails, highest black bit, or finite ancestry? | An unbounded invariant or an exact obstruction. Finite ancestry recovery from an entire trace remains conjectural. |
| D — Actual finite right feedback | Can the finite right half, coupled to a hypothetical periodic center, force an incompatibility with the left reconstruction? | A driver-specific absorption/separation theorem or another representation with a proved interface. Do not assume stabilization from periodic input. |
| E — Nonlocal structure | Is there a useful global order, renormalization, automaton-group action, or finite-support invariant beyond local feature sums? | State precisely what forces progress under infinite trace equality. Decode a fitted potential symbolically before formalizing it. |
| F — Another equivalent route | Use an official sufficient condition or equivalent form: irrationality, nonrational F2 series, unbounded linear complexity, or another route. | A concrete unbounded estimate or proof mechanism with its bridge to the official statement. Another restatement alone is not an advance. |
| G — Independent red team | Audit a promising claim, reproduction, hypothesis, or purported infinite counterexample. | A verified repair, precise counterexample, missing assumption, or independent full kernel replay. |
| H — Your existing or unexpected idea | Bring a mechanism outside these approaches. | Explain what it makes possible, its quickest falsification test, and what it could prove if it survives. |

Solving Q01 or excluding unrestricted period two would be substantial progress,
but would still leave other periods. Keep the full Problem 1 objective intact.

## Failed shortcuts and limits of current evidence

**Proved counterexamples and obstructions:**

- Unrestricted backward observation recovery is false: parents `6/5` have
  different initial observed bits and equal observations at every later time.
  This does not refute age recovery or a seed-specific backward argument.
- The full-row `2*n+2` recovery horizon is false: rows `33/45`, `c=5`, first
  differ at time 58 despite six-bit starts. Their highest bits agree.
- Short ancestry recovery fails for `49/42`, `c=2`, first difference 17:
  one has a natural predecessor and the other has none. Their edges agree.
- Tighter edge bounds `2*n-1` and `2*n-c` fail for `77/56`, `c=1`, first
  difference 13. **The edge-only `2*n+2` candidate remains open.**
- The unbounded response-state example above refutes boundedness under the
  two forward terminal rewrites, even with constant observed output.

See the linked sources and reports before using any of these statements.

**Exploratory evidence, not kernel-checked premises:**

- An apparently successful lexicographic seed-row rank reduced to a detector
  of an imminent observation mismatch. It is constant when three consecutive
  observations agree, so it provides no descent under entire-trace equality.
- Local/nonlocal feature fits have not produced an accepted global rank.
  A particular additive anti-diagonal letter-count family also has exact
  finite arithmetic dual obstructions. This does not exclude other ranks.
- Simple 2-adic polynomial identities for `F(u)` failed modular tests through
  degree six in each variable. This is not a general transcendence theorem.
- Finite future tests distinguish 885 residual functions of the odd decoder;
  zero-prefix tests retain increasingly detailed dependence on prefix length.
  Neither a finite-state nor an infinite-state theorem has been proved.
- There was no shared black checkpoint beyond the initial odd cell in the
  first 2048 outputs across all 16 four-bit even inputs. Larger or more
  structured checkpoint statements remain possible.

A different representation, a new invariant, or a rigorous counterexample can
reopen a direction. Explain what changes. Do not present these exploratory
checks as formal barriers, and do not merely extend a search bound as the
main claimed contribution. Explicitly bounded work is welcome as a
falsification test, implementation check, or guide toward an unbounded proof.

## Verification and publication rules

To reproduce a package already checked at the current pin, run this from
your research clone, using your own prepared official checkout and output:

```text
python research/even-depth-decoder/verify.py --project <3eca23c-reference-checkout> --lake <lake> --output <your-audit-directory>
```

Some older packages and reports are pinned to `2f63afd`, not `3eca23c`.
Follow each package's recorded pin and instructions, or explicitly port and
freshly replay it. Do not change a pin in a manifest and treat an old pass as
a new one. A dependency already built in someone else's workspace is not a
portable source artifact.

Exploration is welcome before Lean formalization. Label it honestly. To report
a kernel-checked theorem, preserve the original checker and official
definitions; rebuild the exact source and replay **all** its declarations.
No `sorry`, new `axiom`, `native_decide`, `decide +native`, or `bv_decide`.
Do not shadow `Ruliology` or silently replace imported statements.

Typical partial check:

```text
lake env lean --run Check.lean YourModule --claim partial --headline YourNamespace.theorem
```

For a full proof candidate, prove `Rule30Submission.problem1` with the exact
official `Problem1` type and run the unchanged checker with `--claim problem1`.
For a disproof candidate, prove `Rule30Submission.not_problem1` with the exact
type `¬ Problem1` and use `--claim not_problem1`. Return the complete source,
dependency hashes, commands, and full checker JSON.
Research helpers may be used locally if their exact sources and verification
are included; a prize module must meet the verifier's allowed-import rules.

Use independent physical truth-table or Wolfram `CellularAutomaton[30]`
controls for packing, orientation, and boundary conventions. Stay inside the
causal cone: an artificial finite boundary can fabricate agreement. Report
all limits, seeds, incomplete domains, timeouts, and counterexamples.

On Troy's shared machine, the current per-owned-job limits are 8 GiB RSS,
at least 2 GiB system memory free, and 300 seconds. Stop only your own process
tree when a guard triggers. Separate build directories prevent agents from
clobbering each other. Do not change the computer's configuration or repeat
Wolfram activation/cloud-login steps.

The isolated 64 GB worker uses the explicit per-experiment limits in the
[memory report](coordinator/20261024-seven/MEMORY-AND-NEW-TARGET.md): 24 GiB
for one large probe replay, or three concurrent 8 GiB partition jobs, with
at least 16 GiB system RAM free. These exceptions do not change the original
host's limits. Record resource stops separately from successful proof checks.

Local full kernel replay, Wolfram backend verification, human review, kit
adoption, and a prize award are different statuses. Record the status actually
supported by evidence. The coordinator will reproduce useful findings before
integrating them into an argument or preparing a new essay for Troy's review.
