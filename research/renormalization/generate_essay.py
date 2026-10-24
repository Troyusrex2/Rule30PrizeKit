"""Generate a review essay with exact embedded standalone source; never submits."""
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
modules = {'Rule30SpacingRenormalizationResearch': 'Spacing',
           'Rule30PackedReconstructionResearch': 'Packed',
           'Rule30SpacingGapCounterexampleResearch': 'Gap',
           'Rule30DrivenPrefixResearch': 'Driven',
           'Rule30Certificates.DrivenEmptyWall': 'DrivenWall',
           'Rule30EmptyGateSpacingResearch': 'EmptyGate',
           'Rule30Certificates.DrivenEmptyCore': 'DrivenCore',
           'Rule30EmptyGateLanguageResearch': 'EmptyLanguage',
           'Rule30ExactReturnResearch': 'ExactReturn'}
parts = []
for module in modules:
    source = (ROOT/'lean/Ruliology/CellularAutomata'/Path(module.replace('.','/')).with_suffix('.lean')).read_text(encoding='utf-8')
    source = source.removeprefix('module\n').replace('@[expose] public section','')
    source = re.sub(r'^public import .*\n', '', source, flags=re.MULTILINE)
    for old, new in modules.items():
        source = source.replace('Ruliology.CellularAutomata.'+old, 'Rule30Submission.'+new)
        source = source.replace(old, 'Rule30Submission.'+new)
    source = source.replace('DrivenEmptyCore.', 'Rule30Submission.DrivenCore.')
    # The data namespaces are renamed above; their former parent namespace
    # is not present in this standalone import closure.
    source = source.replace(' Rule30Certificates\n', '\n')
    parts.append(source.strip())
source = ('import Ruliology.CellularAutomata.Rule30ZeroBoundary\n'
          'import Ruliology.CellularAutomata.Rule30Prize\n\n'
          'import Ruliology.CellularAutomata.Rule30PeriodTwoSideways\n\n'
          'open Ruliology.CellularAutomata\n\n'+'\n\n'.join(parts)+'\n')
(HERE/'Rule30RenormalizationStandalone.lean').write_text(source,encoding='utf-8',newline='\n')
headlines = ['Rule30Submission.Spacing.reconstruction_translate',
             'Rule30Submission.Spacing.transform_spaced_iff',
             'Rule30Submission.Spacing.second_translation_fails',
             'Rule30Submission.Gap.no_uniform_gap_bound_sixteen',
             'Rule30Submission.EmptyGate.empty_spaced',
             'Rule30Submission.EmptyGate.empty_next_gap',
             'Rule30Submission.EmptyGate.transformed_empty_not_spaced',
             'Rule30Submission.EmptyLanguage.no_successive_short_gaps',
             'Rule30Submission.EmptyLanguage.windowWord_allowed',
             'Rule30Submission.ExactReturn.translation_iff_nearSpaced',
             'Rule30Submission.ExactReturn.transformed_exactReturn_iff',
             'Rule30Submission.ExactReturn.empty_gate_fails_arbitrarily_late',
             'Rule30Submission.ExactReturn.empty_second_translation_fails']
config = {'SourceFile':'Rule30RenormalizationStandalone.lean',
          'EssayFile':'renormalization-essay.md','Headlines':headlines}
(HERE/'notebook-config.json').write_text(json.dumps(config,indent=2)+'\n',encoding='utf-8',newline='\n')
probe = (HERE/'spacing-probe.wl').read_text(encoding='utf-8')
gap_probe = (HERE/'spacing-gap-probe.wl').read_text(encoding='utf-8').split('\n',1)[1]
essay = '''---
Template: ComputationalEssay
Name: Empty-right gate spacing and the limits of reconstruction iteration
Author: Troy Lowry; OpenAI Codex
Date: 2026-10-24
Description: An all-time driven-gate invariant, reconstruction identity and exact iteration obstruction
Abstract: Certified 16-cell forward invariants prove exact spacings three or five in the empty-right driven gate from white cycle 146 onward, and exclude consecutive gaps of three from cycle 155 onward. The exact condition for its eight-column reconstruction return is weaker than spacing, but the actual transformed gate violates even that condition arbitrarily late. Its universal twice-transformed formula is false. Two checked examples also refute unconditional iteration and a universal sixteen-cell white-gap bound. The reconstructed left row is not proved infinite, and no prize problem or eventual period two is excluded.
Keywords: [Rule 30, reconstruction, renormalization, Lean, counterexamples]
---

## Scope and source

This essay is prepared for human review and has not been submitted to the prize
API. It proves an unbounded driven-gate spacing theorem, a structural identity,
and exact obstructions to stronger extrapolations. It does not prove CQ01Empty,
exclude eventual period two or solve a prize problem. The empty-right gate is
realized by the actual driven system; no finite-right realization of the separate
period-five or period-31 example gates is asserted.

The one-step identity follows the informal identity in
[morpholib Theorem 14](https://github.com/fractastical/morpholib/blob/777865115483d310f72f0b9511b45409e330a8f5/docs/RULE30_PRIZE_SUBMISSION.md).
That source is credited for the identity. The Lean formalization, support
transfer, exact preservation criterion, packed-cone soundness theorem and
counterexamples here were developed by Troy Lowry with OpenAI Codex. No claim
of literature priority is made. The source's advertised global period-two
elimination is not used as a premise.

## The identity and its required condition

Let b_G(2r)=!G(r), b_G(2r+1)=1 and D G(r)=G(r+2) xor G(r+4).
Call G spaced when black cells never have distance one or two.
For every spaced G, every m >= 1 and every time t, the kit's scalar
reconstruction satisfies

    recon b_G (m+8) t = recon b_(D G) m t.

An initial support bound W transfers to W-8. The preservation criterion is
exact: D G is spaced if and only if G(r+4)=0 for every r. Thus this particular
spacing hypothesis cannot be carried through a second step for an infinite
gate. Other renormalizations remain possible.

The exact weaker condition can also be characterized: the full eight-column
formula at every reconstructed depth holds if and only if adjacent black
gates are forbidden, and distance-two black pairs are forbidden starting
at index one. Only the pair at indices zero and two is exempted. For a
spaced G, this exact condition holds for D G if and only if G(r+5)=0 for
every r. A gate black only at index four shows that this condition is weaker
than preservation of spacing.

## The actual empty-right gate

Let u(s) be position one at physical time 2s+1 of the right half driven by an
alternating black-first center, starting with an entirely white right half.
Set G(r)=u(146+r). A forward invariant of 13,937 sixteen-cell prefixes contains
the actual prefix at physical time 293. The certificate checks all 262,144
eighteen-bit cases, including every possibility for the two unseen right cells.
It checks both closure and six-cycle gate observations. Induction therefore
proves, at every later time, that black observations are separated by exactly
three or five cycles, and that no six-cycle gate window is all white.

At white cycle 155, physical time 311, the actual prefix enters a smaller,
closed 740-state wall. The refined certificate proves that every eight-bit
gate window, encoded earliest bit first in the least significant position,
belongs to {8,9,16,18,33,36,66,72,132,144}. Thus two gaps of three cannot occur
consecutively. The certificate covers all 2,960 possible two-bit tail
transitions, and induction again covers all future times. This refinement is
a constraint on the gate, not a proof of infinite reconstructed support.

The packed engine is proved equal to the kit's driven evolution, with explicit
tail-dependence lemmas. The search that generated the wall is untrusted; every
certificate case is checked by ordinary kernel reduction. There are no native
decision procedures or added axioms.

The translation applies once to this actual spaced gate. Its transform is
provably not spaced, and violates even the exact weaker return condition
arbitrarily late. The universal twice-transformed scalar formula is false
for this actual gate. Weakening the premise cannot repair this particular
iteration; a different transform or reconstruction mechanism remains possible. Infinitely
many black gate observations do not establish infinitely many black cells in
the reconstructed initial left row. That remaining assertion is CQ01Empty,
which this essay leaves open.

## Independent finite observations

The following scalar reconstruction compares 12,800 cells. It also checks a
period-five counterexample to applying the translation twice, and seventeen
white initial cells at depths 528 through 544 for a period-31 gate whose black
spacings are only three or five. These observations are independently connected
to the kit's scalar reconstruction by Lean below.

```wl
'''+probe+'\n'+gap_probe+'''
{spacingReport[], spacingGapReport[]}
```

The period-five example gives white at depth 17, time 0, where the twice
transformed formula gives black. The period-31 example rules out a universal
maximum white gap of sixteen under the spacing-three/five restriction alone.
It does not rule out every larger gap bound.

## Exact embedded Lean source and full kernel replay

The code imports only the kit's core reconstruction and official statement
modules. The packed-cone soundness theorem states its finite light-cone bound.
The proof contains no new axioms, native decision procedure or custom elaborator.

```wl
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit = Environment["RULE30PRIZE_KIT"];
```

```wl
rule30Submission = LeanImportString['''+json.dumps(source,ensure_ascii=False)+''',
  "ProjectDir" -> $Rule30PrizeKit, "IncludeInternal" -> True];
rule30KernelCheck = rule30Submission["Rule30Submission.Spacing.reconstruction_translate"]["KernelCheck"];
rule30KernelCheck
```

```wl
renormalizationHeadlines = '''+str(headlines).replace("'",'"').replace('[','{').replace(']','}')+''';
Table[<|"Theorem" -> name, "Kind" -> rule30Submission[name]["Kind"],
  "Axioms" -> rule30Submission[name]["Axioms"]|>, {name, renormalizationHeadlines}]
```

The complete declaration replay and standard-axiom checks establish exactly
these partial claims. The universal sixteen-cell bound is negated directly in
`no_uniform_gap_bound_sixteen`. A passing partial headline check does not
establish an official prize target, and human review remains separate.
'''
(HERE/'renormalization-essay.md').write_text(essay,encoding='utf-8',newline='\n')
print('Generated standalone source and one exact embedded source string; no submission made')
