"""Carry both checked proof sources and all finite controls inside one essay.

Generates review artifacts only. Never calls the prize submission API.
"""
import hashlib
import json
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT_COMMIT = 'f6885abec122a9dcbb3160cb69312323bc075dc1'
OWN_COMMIT = '765143dc2bf6d4b85f91df3a60433d80ae30ff85'
REFERENCE = '2f63afda261888e04ec57237290e723190914a1d'
HEADLINES = ['Rule30Submission.erosion_bounded', 'Rule30Submission.white_tail_erosion',
             'Rule30Submission.white_tail_often_departs']


def source(commit, stem):
    name = 'lean/Ruliology/CellularAutomata/' + stem + '.lean'
    return subprocess.check_output(['git', 'show', commit + ':' + name], cwd=ROOT)


def body(raw):
    text = raw.decode('utf-8').removeprefix('module\n')
    text = text.replace('@[expose] public section', '')
    return '\n'.join(line for line in text.splitlines()
                     if not line.startswith(('import ', 'public import '))).strip() + '\n'


def main():
    parent = source(PARENT_COMMIT, 'Rule30EtherThreeErosion')
    own = source(OWN_COMMIT, 'Rule30WhiteTailErosion')
    aliases = '''namespace Rule30Submission

open Ruliology.CellularAutomata
open Rule30Ether Rule30EtherThree

theorem erosion_bounded {F : Nat → Nat → Bool} (hF : IsR30 F)
    (j0 s T R k : Nat) (hk : 1 ≤ k)
    (h0 : ∀ t, T ≤ t → F t 0 = eth j0 s 0 t)
    (hbound : ∀ t, T ≤ t → ∃ p, p ≤ R + (t - T) ∧ F t p ≠ eth j0 s p t) :
    ∃ t, T ≤ t ∧ t ≤ T + 3 * (R - k) + 6 ∧
      ∃ p, 1 ≤ p ∧ p ≤ k ∧ F t p ≠ eth j0 s p t :=
  Rule30WhiteTailErosion.erosion_bounded hF j0 s T R k hk h0 hbound

theorem white_tail_erosion {F : Nat → Nat → Bool} (hF : IsR30 F)
    (j0 s T W k : Nat) (hk : 1 ≤ k)
    (h0 : ∀ t, T ≤ t → F t 0 = eth j0 s 0 t)
    (hW : ∀ p, W < p → F T p = false) :
    ∃ t, T ≤ t ∧ t ≤ T + 3 * (W + 12 - k) + 6 ∧
      ∃ p, 1 ≤ p ∧ p ≤ k ∧ F t p ≠ eth j0 s p t :=
  Rule30WhiteTailErosion.white_tail_erosion hF j0 s T W k hk h0 hW

theorem white_tail_often_departs {F : Nat → Nat → Bool} (hF : IsR30 F)
    (j0 s T W : Nat)
    (h0 : ∀ t, T ≤ t → F t 0 = eth j0 s 0 t)
    (hW : ∀ p, W < p → F T p = false) :
    ∀ N, ∃ t, N ≤ t ∧ F t 1 ≠ eth j0 s 1 t :=
  Rule30WhiteTailErosion.white_tail_often_departs hF j0 s T W h0 hW

end Rule30Submission
'''
    standalone = ('import Ruliology.CellularAutomata.Rule30Prize\n'
                  'import Ruliology.CellularAutomata.Rule30EtherThree\n\n'
                  + body(parent) + '\n' + body(own) + '\n' + aliases)
    embedded = 'import Rule30PrizeKit\n' + standalone
    (HERE / 'Rule30WhiteTailErosionStandalone.lean').write_text(
        standalone, encoding='utf-8', newline='\n')
    controls = (ROOT / 'research/overnight/white-tail-erosion-check.wl').read_text(encoding='utf-8')
    assert controls.count('whiteTailErosionReport[path_String]') == 1
    controls = controls.replace('whiteTailErosionReport[path_String]',
                                'whiteTailErosionReport[data_Association]')
    controls = controls.replace('Module[{data,cols,eth,advance,cases}',
                                'Module[{cols,eth,advance,cases}')
    controls = controls.replace('  data=Import[path,"RawJSON"];\n', '')
    data = (ROOT / 'research/overnight/white-tail-erosion-control-cases.json').read_text()
    controls += '\ncontrolData=ImportString[' + json.dumps(data) + ',"RawJSON"];\n'
    controls += 'whiteTailErosionReport[controlData]\n'
    abstract = ('For every Rule 30 evolution of the right half whose boundary follows the '
        'period-three ether from time T, whiteness beyond W at T forces every prefix 1..k '
        'to depart from the matching ether by T + 3 max(W + 12 - k, 0) + 6, for every k >= 1 '
        '(Rule30Submission.white_tail_erosion). Column one departs arbitrarily late '
        '(white_tail_often_departs). Spatial width, phase, transient and initial word are arbitrary. '
        'The earlier erosion theorem of Luis Perez Morales and Claude treats finite perturbations '
        'of the ether, which have a rightmost defect. A white tail instead has infinitely many '
        'ether defects. The new argument replaces a rightmost defect by a defect witness bounded '
        'by an edge of speed one (erosion_bounded). A consecutive run of the earlier proof\'s bad '
        'front state advances by at least eight per step, so it is finite; its unchanged '
        'good-state potential then forces erosion. Locality and one spatial period of the ether '
        'supply the witness. This is an extension of a partial result. No eventual center period '
        'is excluded, no optimal deadline is claimed, and arbitrary infinite right sides remain open.')
    essay = r'''---
Template: ComputationalEssay
Name: Period-three ether erosion with a white right tail
Author: Troy Lowry; OpenAI Codex
Date: 2026-10-24
Description: An unbounded extension from finite ether perturbations to a white tail
Abstract: __ABSTRACT__
Keywords: [Rule 30, ether, finite support, Lean, partial result]
ContextPath: ["Wolfram`LeanLink`"]
---

## The result and its scope

Let F(t,p) be a Rule 30 evolution for columns p >= 1. Column zero is driven
by the period-three ether E(j,t), at any attachment j0 and phase s, from
time T onward. Suppose F(T,p)=0 for every p>W. For every k>=1 there is a
time t and a column p such that

    T <= t <= T + 3 max(W + 12 - k, 0) + 6,
    1 <= p <= k, and F(t,p) != E(j0+p,t+s).

The prefix need not match initially: if it already differs, t=T works.
Restarting the argument at later times shows that column one departs from
its matching ether profile arbitrarily late. The two headline theorems are
`Rule30Submission.white_tail_erosion` and `white_tail_often_departs`.

This does not prove or disprove a Rule 30 Prize problem. In particular,
departing from one matching ether profile does not rule out other periodic
profiles. The eventual-period-three center question remains open.

```wl
ArrayPlot[CellularAutomaton[30,{{1},0},{48,{-48,48}}],Frame->True,
  PlotLabel->"Rule 30 from a single black cell"]
```

## What is new, and what is reused

Luis Perez Morales and Claude (Fable 5.1) proved that every finite perturbation
of the period-three ether erodes into an initially matching prefix, and that
there is no finite ether wall of any width (submission R30-20261024-1fc962,
kit PR #10). Their proof follows the first defect. Of its 24 local states,
23 have a decreasing potential. A run of the remaining bad state advances
by at least eight columns per step, whereas the rightmost defect moves by one.

A white tail is an infinite perturbation of the ether, with no rightmost
defect. The new `erosion_bounded` needs only a defect witness at a position
at most R+(t-T) for every t>=T. The first defect cannot exceed that witness.
The earlier bad-state and potential arguments then apply. A white tail
supplies R=W+12: its support grows at most one cell per step, and among the
next twelve ether cells there is a black cell. The bound twelve is convenient,
not claimed optimal. This changes the permitted right sides, with no finite
width or temporal-clock limit.

PR #11 contains the new catalog module and explicitly depends on #10. The
source below carries both proofs because #10 is not installed in the current
reference kit. The earlier proof, its certificate and its potential remain
credited to their original authors. No priority claim is made for those results.

## An explicit driven evolution

The boundary here is imposed externally. The image shows the difference
from the matching ether for a finite right word; the initially matching
prefix has length fourteen, and first departs at time twenty-four. This is
one illustration, not the proof of the unbounded quantifiers.

```wl
etherColumns=IntegerDigits[FromDigits[#,2],2,3]& /@
  {"001","001","011","110","010","010","110","101","100","100","101","011"};
ether[j_,t_]:=etherColumns[[Mod[j,12]+1,Mod[t,3]+1]];
halfStep[a_,b_]:=BitXor[BitOr[BitShiftLeft[a,1],b],BitOr[a,BitShiftRight[a,1]]];
exampleRows=FoldList[halfStep[#1,ether[4,#2]]&,17619461964066119253545154634814,Range[0,39]];
exampleDifference=Table[BitXor[BitAnd[BitShiftRight[exampleRows[[t+1]],p-1],1],
  ether[4+p,t]],{t,0,40},{p,1,120}];
ArrayPlot[exampleDifference,Frame->True,ImageSize->Large,
  PlotLabel->"Black marks a defect from the ether; the first fourteen columns depart at time 24"]
```

## Independent built-in Rule 30 controls

The following twelve computations use finite arrays with margins large
enough to isolate each causal cone. Until the first prefix departure, the
physical boundary is still the matching ether, so it agrees with the imposed
driver. No agreement after that time is asserted. All data is embedded here.
The scalar update and every departure time are checked against built-in
Rule 30. These finite controls check examples and coordinates, not the theorem.

```wl
__CONTROLS__
```

## The full Lean proof

The source contains the unchanged mathematical proof bodies of PR #10 at
f6885abec122a9dcbb3160cb69312323bc075dc1 and of the new module at
765143dc2bf6d4b85f91df3a60433d80ae30ff85. Only their module/import/export
wrappers are removed for this single-file environment. Three named aliases
expose the new claims under `Rule30Submission`. No unmerged module is imported.

```wl
Needs["Wolfram`LeanLink`"];
$Rule30PrizeKit=Environment["RULE30PRIZE_KIT"];
```

```wl
rule30Submission=LeanImportString[__LEAN_SOURCE__,"ProjectDir"->$Rule30PrizeKit]
```

## Formal statements and full kernel replay

The following checks replay the entire module, including the carried
dependency. The headline statements and their axioms are read directly from
the same evaluated Lean environment.

```wl
rule30KernelCheck=rule30Submission["Rule30Submission.white_tail_erosion"]["KernelCheck"];
<|"FullModuleReplay"->rule30KernelCheck,
  "Headlines"->Association@Table[name-><|
    "Type"->rule30Submission[name]["TypeForm"],
    "Axioms"->rule30Submission[name]["Axioms"]|>,
    {name,{"Rule30Submission.erosion_bounded","Rule30Submission.white_tail_erosion",
      "Rule30Submission.white_tail_often_departs"}}]|>
```

The first new lemma removes the rightmost-defect premise. `white_tail_evol`
proves the support bound by induction; `white_tail_defect` uses the ether's
spatial period to supply the general theorem's witness. The final lemma
restarts at an arbitrary later time to prove arbitrarily late departures.
These statements expose the remaining hypotheses, rather than assuming any
unproved finite-support or center-period reduction.

```wl
Association@Table[name->rule30Submission[
  "Ruliology.CellularAutomata.Rule30WhiteTailErosion."<>name]["TypeForm"],
  {name,{"run_bad_bounded","white_tail_evol","white_tail_defect"}}]
```

## What remains open

The prize's center column is not an ether-driven boundary supplied by this
theorem. No proof of `Q001`, `C3w(011)`, or any center-period exclusion is
obtained. For arbitrary infinite right sides, the bounded defect-witness
premise is not established. Finding such a premise where the full coupled
problem requires it is additional mathematical work. Local verification of
this essay is not a Prize Committee decision or an official submission status.

## References

- Luis Perez Morales and Claude (Fable 5.1), [The Period-3 Ether Erodes](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261024-1fc962), [kit PR #10](https://github.com/WolframInstitute/Rule30PrizeKit/pull/10).
- Troy Lowry with OpenAI Codex, [white-tail extension, kit PR #11](https://github.com/WolframInstitute/Rule30PrizeKit/pull/11).
- [Reference kit at 2f63afd](https://github.com/WolframInstitute/Rule30PrizeKit/tree/2f63afda261888e04ec57237290e723190914a1d), including the ether definition and unchanged checker.
'''
    for marker, replacement in [('__ABSTRACT__', abstract), ('__CONTROLS__', controls),
                                ('__LEAN_SOURCE__', json.dumps(embedded, ensure_ascii=False))]:
        assert essay.count(marker) == 1
        essay = essay.replace(marker, replacement)
    (HERE / 'white-tail-erosion-essay.md').write_text(essay, encoding='utf-8', newline='\n')
    (HERE / 'notebook-config.json').write_text(json.dumps({
        'SourceFile': 'Rule30WhiteTailErosionStandalone.lean',
        'EssayFile': 'white-tail-erosion-essay.md', 'Headlines': HEADLINES}, indent=2)+'\n',
        encoding='utf-8', newline='\n')
    manifest = {'reference_commit': REFERENCE, 'dependency_commit': PARENT_COMMIT,
                'catalog_commit': OWN_COMMIT, 'headlines': HEADLINES,
                'dependency_authors': 'Luis Perez Morales; Claude (Fable 5.1)',
                'extension_authors': 'Troy Lowry; OpenAI Codex (GPT-6)',
                'parent_source_sha256': hashlib.sha256(parent).hexdigest(),
                'extension_source_sha256': hashlib.sha256(own).hexdigest(),
                'embedded_source_sha256': hashlib.sha256(embedded.encode()).hexdigest(),
                'standalone_body_sha256': hashlib.sha256(standalone.encode()).hexdigest(),
                'proof_body_adaptation': 'module/import/export wrappers only; no body changes',
                'new_headline_aliases': len(HEADLINES), 'full_problem_claim': False,
                'prize_api_submitted': False, 'human_approval_pending': True}
    (HERE / 'source-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n',
                                             encoding='utf-8', newline='\n')
    print(json.dumps({'standalone_lines': len(standalone.splitlines()),
                      'embedded_bytes': len(embedded.encode()),
                      'abstract_words': len(abstract.split()), 'prize_api_submitted': False}))


if __name__ == '__main__':
    main()
