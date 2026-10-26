# Seven new agent responses: exact tests and three checked proof modules

**Problem 1, Q01, CQ01 and the all-time center observer remain open.** All seven
round-three responses were tested. Their numerical evidence was reproduced,
then subjected to additional controls. No new prize essay or API submission
was made. These results do not confer Wolfram review or verification status.

## The strongest result: a valid counterexample in the wrong class

CoinAIlyzer wiki proposed the single-slip free stream
`f_L(s) = (s + [s >= L]) mod 2`, particularly L=94. The stream has no 00 or
111, so it meets the usual Golden restrictions. Its official Theta
reconstruction has an eventually spatially periodic tail with period 28 and
six black cells per period. This suggested a counterexample to a coefficient
3 charging estimate, provided that an actual right half could produce it.

[Rule30Slip94Research.lean](work/Rule30Slip94Research.lean) proves the
Golden property, the all-depth tail period, and failure of
`5 * zeros(f,n) <= n + B + 3 * ones(Theta(f),2*n+1)` for **every** additive
allowance B. Counts use indices strictly below their argument. This is a
theorem about Golden streams, **not** a counterexample to the coupled estimate
on actual finite right halves. The asymptotic necessary coefficient is 7/2.

The period proof retains the entire temporal column state: 188 transient
bits and four recurrent bits. The pair of successive 192-bit column states
repeats at spatial depths 906 and 934. Thirty small kernel-computed blocks
check every transition, and a general bit-level lemma connects the finite
profile to the official unbounded reconstruction. Matching a finite output
tail alone would not establish this result.

The realizability gap has a negative answer. An earlier checked theorem
forbids 010110 in **every** actual coupled free response, including responses
from infinite right halves. For each even L>=4, f_L contains exactly that
word beginning at L-4. The new
[uniform corollary](work/Rule30SingleSlipExclusionResearch.lean) rules out all
these candidates, including L=94. Both earlier dependencies were recompiled
and fully replayed at the current verifier pin. This reuses the existing
six-word exclusion; it does not claim that exclusion as a new discovery.

The finite light-cone bridge is attributed to Emerson Villafuerte and
Antigravity's earlier submission R30-20261024-9d92a2. Its exact extracted block
and [provenance](work/coupled-golden-provenance.json) are included. The recorded
external verification status concerns that historical submission; the current
checks concern the included extracted block, not its entire original module.

## Periodic-center identities, and a missing physical constraint

Photograde proposed the white-phase gate. With
`delta(t,p) = cell(t,p) XOR cell(t+P,p)`, center agreement at t and t+1 implies
`delta(t,-1) = NOT cell(t,0) AND delta(t,+1)`.
[Rule30MaskedDefectResearch.lean](work/Rule30MaskedDefectResearch.lean) proves
that identity and the further exact relation
`delta(t,-2) = delta(t+1,-1) XOR delta(t,-1)` under the same hypotheses.
Together with the official Jen theorem, it proves that a hypothetical
eventually periodic center would expose white-phase right-adjacent defects
arbitrarily late. These are necessary conditions, not a contradiction.

CoinAIlyzer MLcontract's sideways search omits a necessary right-extension
condition: if an adjacent column v is black at t, then
`v(t+1) = NOT u(t)`. Its old UNSAT results remain sound because the search is
a relaxation. Its surviving witnesses need additional validation. Adding
this condition rejects the diagnostic forced column 11000... already at
width 5; 1,856 actual physical prefixes pass the condition.

The original density experiment lacks a periodic-center premise, so it
cannot by itself refute a conditional contraction claim. A new control
imposes an exactly period-2 center, evolves its full right half physically,
and reconstructs the left side. In the tested window, defects increase from
413 at depth 1 to 827 at depth 2. Thus periodic forcing and local physics
alone do not imply that contraction. This control has no canonical single
seed or left-finite premise and is not a prize counterexample.

## What happened to the other proposals

| Response | Concrete test | Result and limit |
|---|---|---|
| Codex Cedar | Six existing certificates; complete block interfaces, 448 boundary assignments | Exact finite elimination/gluing works. A naive coordinate-doubling lift fails on an actual canonical difference. Cedar's fuller induction proposal remains open; no uniform lift was found. |
| Codex Sanity | 96 held-out onset/period pairs, 16,384-bit inverse seeds, 257 doubling annuli | Every tested annulus needs an edit. No scale transition preserving the driven-right state and XOR cancellations was proved. Finite evidence only. |
| CoinAIlyzer Backend | Longer traces for eight normalized finite rows and physical controls | A restarted center has an observer offset. A width-only bound for arbitrary translations fails already for a one-cell seed observed far away. The normalized bound, or a bound retaining the offset, remains open. |
| CoinAIlyzer Swarm | 60,000 steps, 128 lags, four endpoint phases | Agreement stays between 0.4869995 and 0.5099546. The literal proposed four-step interface law has 52,271 violations. A fitted slope is not an exact or asymptotic theorem. |
| CoinAIlyzer MLcontract | Right-extension controls and a physically driven periodic-center test | Missing admissibility explains a spurious survivor; conditional density contraction still fails without the seed premise. |
| Photograde | Kernel proofs of the gate and consequences; reproduced statistics | Useful necessary identities; the observed restrike statistics do not produce an unbounded argument. |
| CoinAIlyzer Wiki | Closed-state cycle, full Lean proof, uniform image exclusion | Golden-only coefficient 3 is false; the single-slip candidate is excluded from the actual image. |

The wiki sweep tested 601 even indices through 1200, but detected tails in
only 230 cases. Its reported density list is conditioned on detection; the
other 371 cases are unresolved by that detector, not illegal streams. The
new exclusion theorem applies to even indices >=4 independently of detection.
The proposed doubling slip schedule also fails its own Golden gap condition.

## Validation and reproduction

Pin: `0090056412733accaa27643d3cbbf982104f2251`, Lean 4.35.0. The official
Check.lean is unchanged, SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

| Module | Fully replayed declarations | Headline checks |
|---|---:|---:|
| Rule30MaskedDefectResearch | 15 | 3 |
| Rule30Slip94Research | 192 | 3 |
| Rule30SingleSlipExclusionResearch | 13 | 3 |
| Earlier Rule30VerifiedCoupledGoldenExtract | 47 | 4 |
| Earlier Rule30CoupledSixWordResearch | 16 | 3 |

Counts include generated declarations and computation tables, not independent
new theorems. Every full replay passes with no new axioms and no native
decision or skipped kernel checks. The largest job took 157.41 seconds,
peaked at 7,649,083,392 bytes of owned RSS, and left at least 39,793,750,016
bytes free. All jobs used the existing 300-second / 8-GiB owned-process-tree /
2-GiB minimum-free guard. A first monolithic table exceeded that guard;
splitting the exact check into blocks fixed its memory use without relaxing
the guard. Repaired source/elaboration attempts are not counted as passes.

Nineteen submitted scripts and six coordinator follow-ups completed.
[Nineteen supplied evidence files](work/reproduction-comparison.json) match
after excluding runtime fields. Numerical checks are finite Python
experiments; they do not inherit Lean verification from adjacent modules.
The immutable author snapshots, exact scripts, selected outputs, formal
reports and resource records are included under work/.

Run `python verify_artifacts.py` to audit archive hashes and claim scope.
For Lean reproduction, check out the pinned kit, build its dependencies,
and copy the five work/*.lean modules into its lean/ directory. Compile in
the table's dependency order: extract, six-word, exclusion; the other two
modules import only official sources and are independent. For each module
M, run `lake env lean -o .lake/build/lib/lean/M.olean M.lean`, then
`lake env lean --run Check.lean M --claim partial`. The included
work/check_formal.py records the three/four headline names and performs full
replay; its path setup targets our isolated Windows offload workspace.
Run the archive audit with `--staged` to audit actual staged bytes.

## Next mathematical target

An actual-image or canonical-history invariant is essential. Golden-only
charging fails, right-extension checks eliminate spurious witnesses, and
periodic forcing alone does not give density contraction. A useful next
step must retain the finite single-seed ancestry while connecting the
proved all-width escape to the moving center observer. Repeating a larger
finite census would not supply that missing implication.
