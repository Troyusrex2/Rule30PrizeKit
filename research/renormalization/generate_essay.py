"""Generate a review essay with exact embedded standalone source; never submits."""
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
modules = {'Rule30SpacingRenormalizationResearch': 'Spacing',
           'Rule30PackedReconstructionResearch': 'Packed',
           'Rule30SpacingGapCounterexampleResearch': 'Gap'}
parts = []
for module in modules:
    source = (ROOT/'lean/Ruliology/CellularAutomata'/(module+'.lean')).read_text(encoding='utf-8')
    source = source.removeprefix('module\n').replace('@[expose] public section','')
    source = re.sub(r'^public import .*\n', '', source, flags=re.MULTILINE)
    for old, new in modules.items():
        source = source.replace('Ruliology.CellularAutomata.'+old, 'Rule30Submission.'+new)
        source = source.replace(old, 'Rule30Submission.'+new)
    parts.append(source.strip())
source = ('import Ruliology.CellularAutomata.Rule30ZeroBoundary\n'
          'import Ruliology.CellularAutomata.Rule30Prize\n\n'
          'open Ruliology.CellularAutomata\n\n'+'\n\n'.join(parts)+'\n')
(HERE/'Rule30RenormalizationStandalone.lean').write_text(source,encoding='utf-8',newline='\n')
headlines = ['Rule30Submission.Spacing.reconstruction_translate',
             'Rule30Submission.Spacing.transform_spaced_iff',
             'Rule30Submission.Spacing.second_translation_fails',
             'Rule30Submission.Gap.no_uniform_gap_bound_sixteen']
config = {'SourceFile':'Rule30RenormalizationStandalone.lean',
          'EssayFile':'renormalization-essay.md','Headlines':headlines}
(HERE/'notebook-config.json').write_text(json.dumps(config,indent=2)+'\n',encoding='utf-8',newline='\n')
probe = (HERE/'spacing-probe.wl').read_text(encoding='utf-8')
gap_probe = (HERE/'spacing-gap-probe.wl').read_text(encoding='utf-8').split('\n',1)[1]
essay = '''---
Template: ComputationalEssay
Name: An eight-column reconstruction identity and the limits of its iteration
Author: Troy Lowry; OpenAI Codex
Date: 2026-10-24
Description: A core Lean identity, exact preservation criterion and checked counterexamples
Abstract: For a spaced boundary gate, Rule 30 sideways reconstruction translates eight columns by a simple gate transform. The spacing survives exactly when the original gate is white from index four onward. A period-five gate disproves unconditional iteration, and a period-31 spacing-three/five gate produces seventeen consecutive white initial cells. No prize problem or eventual period two is excluded.
Keywords: [Rule 30, reconstruction, renormalization, Lean, counterexamples]
---

## Scope and source

This essay is prepared for human review and has not been submitted to the prize
API. It proves a partial structural identity and identifies two gaps in stronger
extrapolations. It does not exclude eventual period two or solve a prize problem.
No finite driven-right realization of the example gates is asserted.

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
