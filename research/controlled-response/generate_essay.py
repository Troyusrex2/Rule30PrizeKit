"""Embed the complete two-module proof in a review essay; never submit it."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
modules = {'Rule30ControlledResponseResearch': 'Response',
           'Rule30PeriodicProfileCounterResearch': 'Profiles'}
parts, manifest = [], []
for module in modules:
    path = ROOT/'lean/Ruliology/CellularAutomata'/(module+'.lean')
    source = path.read_text(encoding='utf-8')
    manifest.append({'module': module, 'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    source = source.removeprefix('module\n').replace('@[expose] public section', '')
    source = re.sub(r'^public import .*\n', '', source, flags=re.MULTILINE)
    for old, new in modules.items():
        source = source.replace('Ruliology.CellularAutomata.'+old, 'Rule30Submission.'+new)
        source = source.replace(old, 'Rule30Submission.'+new)
    parts.append(source.strip())
source = ('import Ruliology.CellularAutomata.Rule30Ether\n'
          'import Ruliology.CellularAutomata.Rule30Realization\n'
          'import Ruliology.CellularAutomata.Rule30ZeroBoundary\n\n'
          'open Ruliology.CellularAutomata\n\n'+'\n\n'.join(parts)+'\n')
(HERE/'Rule30ControlledResponseStandalone.lean').write_text(source, encoding='utf-8', newline='\n')
headlines = ['Rule30Submission.Response.'+h for h in [
    'sameResponse_iff_diagonal', 'sameResponse_iff_drv', 'tail_011_drv', 'tail_101_drv',
    'feedback_left_equal', 'tail_011_center', 'tail_101_center',
    'short_window_not_sameResponse', 'fixed_driver_counterexample']]
headlines += ['Rule30Submission.Profiles.'+h for h in [
    'full_period_eight', 'same_OR', 'OR_nonconstant', 'heads_differ',
    'infinite_true', 'infinite_false', 'loss_head_period_two', 'loss_full_period_lower_bound', 'loss_infinite']]
config = {'SourceFile': 'Rule30ControlledResponseStandalone.lean',
          'EssayFile': 'controlled-response-essay.md', 'Headlines': headlines}
(HERE/'notebook-config.json').write_text(json.dumps(config, indent=2)+'\n', encoding='utf-8', newline='\n')
(HERE/'source-manifest.json').write_text(json.dumps({'modules': manifest,
    'standalone_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'standalone_changes': 'Only module/import/export wrappers and namespaces adapted',
    'full_problem_claim': False}, indent=2)+'\n', encoding='utf-8', newline='\n')
probes = '\n'.join((HERE/name).read_text(encoding='utf-8') for name in
                   ['controlled-response-check.wl', 'profile-counter-check.wl'])
essay = '''---
Template: ComputationalEssay
Name: Controlled responses and finite-support observability limits in Rule 30
Author: Troy Lowry; OpenAI Codex
Date: 2026-10-24
Description: Arbitrary-driver response equivalence, sound terminal rewrites, and explicit infinite-tail counterexamples
Abstract: Responses of a right half to every left-boundary input are characterized exactly by two observations of a triangular diagonal map. Terminal rewrites 011 to 01 and 101 to 11 preserve the complete center trace with every common initial left half. Explicit eight-periodic infinite tails show that OR alone need not recover the head and that a period-two head need not detect a full period-eight state. Finite-tail completeness and the Rule 30 Prize problems remain open.
Keywords: [Rule 30, controlled systems, observability, Lean, infinite tails]
---

## Scope and provenance

This is a partial contribution developed by Troy Lowry with OpenAI Codex. It
builds on the kit's driven right half in Rule30Ether and whole-line evolution
in Rule30Realization. No literature-priority claim is made. The essay is
prepared for human review and has not been sent to the prize API.

The terminal rewrites can change a finite row's right edge without changing
its center trace. For example, the two rows with black cells only at positions
{2,3} and {2}, respectively, have identical center traces at every time. Their
left edges agree; this does not refute recovering a left edge from the trace.
The general theorem allows every common initial left half and every shared
finite prefix before the displayed terminal word.

## Exact response equivalence

Index a right-half state x by 0,1,... for physical positions 1,2,... . Define

    Q(x)(k) = x(k) XOR (x(k+1) OR x(k+2)).
    F_b(x)  = (b XOR (x(0) OR x(1))) :: Q(x).

The second formula is exactly one Rule 30 step with left boundary bit b. Two
right states have equal head outputs for every boundary-input sequence and
every time if and only if, for every n, both the head and the OR of the first
two cells of Q^n(x) agree. The infinite response tree is therefore replaced
by two observations along one deterministic orbit. The theorem places no
finite-support restriction on this equivalence.

For every common finite prefix, terminal 011 followed by zeros can be
replaced by 01, and terminal 101 followed by zeros by 11. Both replacements
preserve responses to all boundary inputs for all times. A separate induction
shows that this equivalence remains sound with actual feedback through the
center: if initial left halves, including the center, agree, they agree at
every later time. Thus both terminal rewrites preserve the complete center
trace in the full Rule 30 system, including when both starting rows are finite.

No converse from a single prescribed driver is proved. In fact, right states
1 and 11 have the same head output forever under the constantly zero driver,
but are not universally response equivalent. This driver is not asserted to
extend to a finite whole-line orbit. A second example, packed states 42 and
70, agrees through thirteen observations for every driver but is not
universally equivalent. Checking only 2W-1 observations is insufficient at W=7.

## Why the support and observation hypotheses matter

Write an infinite row from its head toward the right. The two starts

    x = 1100(1101)...
    y = 0110(01)...

use parenthesized blocks repeated forever. Both complete Q orbits have period
dividing eight. Their head traces differ, but the OR of the first two cells
is the same nonconstant sequence at every time. At time two, the next OR,
of cells one and two, differs. The common OR alone cannot recover the head
or the next OR. These states are not universally response equivalent, because
that relation observes the head as well.

A third start, 1100(0001)..., has a head trace of least period two, whereas its
complete Q orbit has least period eight. All three starts are proved to have
infinite support. A power-of-two orbit period cannot replace finite support
in a proposed head-period detection theorem. No finite-tail conjecture is
refuted or proved by these examples.

The proofs use explicit temporal profile tables, verify their scalar update
at every depth, and then identify all iterates by induction. The finite search
that found the tables is not a proof premise. No part of this essay excludes
an eventual center period or proves a Rule 30 Prize problem.

## Independent finite controls

The first calculation compares terminal rewrites in 104 complete Rule 30
experiments with random common left halves and prefixes. The second compares
all three profile tables with built-in Rule 30 on finite causal cones.
These controls do not replace the unbounded kernel proofs.

```wl
'''+probes+'''
{controlledResponseReport[], profileCounterReport[]}
```

The diagram shows eight times, from top to bottom, and the first twelve cells
of each infinite row. Black squares are black cells. The right tail repeats
from position four. The last panel's first column alternates while later
columns require eight times to repeat; the all-time claims are proved below.

```wl
profileCounterDiagram[]
```

## Exact embedded proof and full kernel replay

The source below contains both complete catalog modules, with only imports,
module/export wrappers and namespace names adapted for a standalone file.
It imports only official core modules and uses no additional axioms or native
decision procedures. A passing partial check does not establish an official
prize target.

```wl
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit = Environment["RULE30PRIZE_KIT"];
```

```wl
rule30Submission = LeanImportString['''+json.dumps(source, ensure_ascii=False)+''',
  "ProjectDir" -> $Rule30PrizeKit, "IncludeInternal" -> True];
rule30KernelCheck = rule30Submission["Rule30Submission.Response.sameResponse_iff_diagonal"]["KernelCheck"];
rule30KernelCheck
```

```wl
responseHeadlines = '''+json.dumps(headlines).replace('[','{').replace(']','}')+''';
Table[<|"Theorem" -> name, "Kind" -> rule30Submission[name]["Kind"],
  "Axioms" -> rule30Submission[name]["Axioms"]|>, {name, responseHeadlines}]
```

Finite-tail normal-form completeness, actual fixed-driver trace rigidity and
the full center-column problem remain open. No new prize essay is submitted
by this build.
'''
(HERE/'controlled-response-essay.md').write_text(essay, encoding='utf-8', newline='\n')
print('Generated exact standalone source and review essay; no API call')
