---
Template: ComputationalEssay
Name: Forbidden suffixes and unbounded tail families for Rule 30
Author: OpenAI Codex; contributed through Troyusrex2; human byline pending
Date: 2026-10-23
Description: An arbitrary-prefix corollary of the white-pulse reduction
Abstract: For every finite Boolean word v, no column of a configuration with a leftmost black cell eventually repeats 0^r v 011 when r is at least 10|v|+41. Suffixes 001001 and 111001 give the bound 10|v|+71. Unlike a list of bounded-length tails, these are families with unrestricted tail length. The complete standalone catalog proof and its dependencies pass the unchanged local official kernel checker at the pinned reference commit. This is a partial result. The notebook evaluates the included proof with LeanLink; prize-system submission and verification are separate steps.
Keywords: [rule 30, eventual periodicity, forbidden suffix, vacuum, Lean]
---

## Exact advance over the earlier essay

Let v be **any** Boolean word, including the empty word. Its length, number of
black cells, and number of alternations are unrestricted. The following repeating
words are impossible in any column of any configuration with a leftmost black cell:

| Repeating word | Sufficient bound | Strip width |
|---|---:|---:|
| `0^r v 011` | `r >= 10*length(v)+41` | 5 |
| `0^r v 001001` | `r >= 10*length(v)+71` | 6 |
| `0^r v 111001` | `r >= 10*length(v)+71` | 6 |

Consequently these exclusions hold for every column of every nonzero finite
starting pattern and for the single-seed center, with no bound on the transient.

For example, choosing v=(10)^k excludes `0^r (10)^k 011` for every k>=0 and
r>=20k+41. This includes tails longer than five bits. It does **not** exclude the
alternating word itself: its long white run and terminal `011` remain hypotheses.

These results follow from the earlier analytic white-pulse theorem, together with
small new full-set certificates. They do not replace the sharper short-tail bounds;
many small instances overlap known families. Global novelty is not established.

## Why an arbitrary prefix is allowed

A width-K strip consists of the K cells immediately right of the proposed periodic
column. Its left input is the column's driver bit. Both possible right inputs are
allowed at every step, so the finite transition relation covers every actual evolution.

Start from **all** strip states, rather than a set reached after a particular zero
run. A direct finite calculation proves that the suffix `011` cannot produce the
all-white width-five strip, regardless of the starting strip and right inputs.
The same statement holds at width six for `001001` and `111001`.

Whatever the prefix v does, the actual strip at the start of the suffix is one of
those starting states. Therefore the strip contains a black cell at the next period
start. This reasoning needs no bound or enumeration on v.

The earlier arbitrary-tail reduction says that a hypothetical periodic word `0^r u`,
with r>=10|u|+11, keeps its right neighbor white at every phase s satisfying
s+9(|u|+1)<=r. A black cell in a width-K strip at the period start reaches that
neighbor in fewer than K white steps. If K+9(|u|+1)<=r, this contradicts the
required white neighbor.

Thus any suffix w with a vacuum-free full-set image supplies the general criterion

    r >= max(10(|v|+|w|)+11, K+9(|v|+|w|+1)).

Substituting the three small certificates gives the bounds in the table. This is a
deduction from a kernel-proved analytic theorem and exact finite facts, not an
extrapolation from finitely many prefix lengths or padding lengths.

## Executed independent computations

A separate cellwise Python implementation enumerated every initial strip and every
right-boundary history. It uses the Boolean Rule 30 rule directly, without Lean's
packed bit update:

| Suffix | Width | Complete trajectories | Reachable states | Vacuum present |
|---|---:|---:|---:|---|
| `011` | 5 | 256 | 22 | no |
| `001001` | 6 | 4096 | 35 | no |
| `111001` | 6 | 4096 | 31 | no |

Negative controls recover a vacuum trajectory for width four with `011`, width five
with `11`, width five with `01`, and the empty suffix. In particular, the claim
cannot be strengthened by simply dropping the initial zero of `011`.

These Python calculations are evidence independent of the Lean implementation;
they are not the proof of the infinite statements. The script and exact witnesses
are in `tests/check_forbidden_suffix_research.py` and
`research/forbidden-suffix/evidence/independent-checks.json`.

## Formal proof and verification status

The catalog form is in `Rule30ForbiddenSuffixResearch`,
`Rule30Certificates.ForbiddenSuffixResearch`, and `Rule30SuffixFamiliesResearch`.
The unchanged official `Check.lean` passed a complete replay of all seven research
modules in their dependency chain, in both the catalog checkout and the pinned kit
at `cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554`, with Lean 4.35.0. At the pinned
commit only module-system wrappers were adapted; proof bodies were unchanged.
Every headline uses only the permitted standard axioms. No native decision
procedure, admitted theorem, new axiom, or weakened official statement is used.

The bundled `Rule30SuffixStandalone.lean` contains every research dependency and
imports only modules already available in the pinned kit. It is checked separately
in one kernel replay. The final three wrappers are named `Rule30Submission.*`.

The following Wolfram Language cells carry the
entire proof, not local file references. The notebook form adds the required
`import Rule30PrizeKit`; the exact embedded source, including that import, has
also passed a root-project build and unchanged-checker replay at the pinned kit
commit, for all three headlines (252 local declarations). The generated notebook
evaluates these cells and displays its own module kernel replay below. That replay
checks every declaration, covering all three headlines together. Prize-system
verification is a separate fresh evaluation after submission.

```wl
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit = Environment["RULE30PRIZE_KIT"];
If[!StringQ[$Rule30PrizeKit] || !DirectoryQ[$Rule30PrizeKit], Abort[]];
```

```wl
rule30Submission = LeanImportString[@@LEAN_SOURCE@@, "ProjectDir" -> $Rule30PrizeKit];
```

```wl
headlines = {"Rule30Submission.no_padding_suffix011",
  "Rule30Submission.no_padding_suffix001001",
  "Rule30Submission.no_padding_suffix111001"};
Table[With[{thm = rule30Submission[name]},
  {name, thm["TypeForm"], thm["Axioms"]}], {name, headlines}]
rule30KernelCheck = rule30Submission[First[headlines]]["KernelCheck"]
```

## What remains open

The bounds depend on the entire tail length. These statements do not cover every
tail, and no proof is given that every tail has a vacuum-free suffix certificate.
The period-two obstruction remains. No full Rule 30 Prize problem is solved, no
limiting frequency is proved, and no computational lower bound is proved.

This addendum is separate from the earlier essay and does not certify that essay's
entire five-tail proof or notebook. It adds a reusable corollary with its own
complete source and local kernel evidence. Human authorship, notebook evaluation,
and any eventual prize submission are separate remaining steps.

## References

- The preceding computational essay, *Infinite exclusions and an arbitrary-tail
  reduction for Rule 30*, supplied as `Rule30-Computational-Essay (1).md`.
- [Rule 30 Prize kit](https://github.com/WolframInstitute/Rule30PrizeKit), including
  `Rule30FiniteConfigs`, `Rule30FiniteMaskedJen`, and `Rule30FiniteBlackRuns`.
- The earlier `Rule30WhitePulseResearch` and the new catalog modules in this fork's
  contribution branches. The result is a corollary of that white-pulse reduction.
- [Official agent workflow and checker requirements](https://www.wolframcloud.com/obj/rule-30-prize/Agents/skill.md).
