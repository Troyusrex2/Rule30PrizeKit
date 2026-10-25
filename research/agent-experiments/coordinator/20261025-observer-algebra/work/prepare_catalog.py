from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
repo=Path(r'D:\MWB\Rule30\observer-barrier-catalog-20261025')
text=(root/'Rule30ObserverBarrierResearch.lean').read_text(encoding='utf-8')
text=text.replace('Rule30ObserverBarrierResearch','Ruliology.CellularAutomata.Rule30DividedDifference')
i=text.index('/-!');j=text.index('-/',i)+2
intro='''/-!
# Divided-difference observers: gauges, a frontier, and a physicality barrier

For fixed actual Rule30 backgrounds A,B, their XOR satisfies the linear rule
`h' = left XOR ((NOT B_right) AND center) XOR ((NOT A_center) AND right)`.
Redistributing the quadratic term gives a local Boolean gauge. The universal
`Front.actual_difference` theorem verifies this for every pair, gauge and time.
The universal
`curvature` identity records the error in treating A XOR h as a new physical
configuration; the error is `h_center AND (delta_right XOR h_right)`.

The counterexample uses A(p)=[p mod3=1] and B(p)=[p mod3=2]. They merge to all
black after one step and vacuum after two. For every k>=1, the auxiliary
initial mode has four black cells at -3k-2,-3k-1,3k+1,3k+2. It is initially
supported inside A XOR B, but its observation at column1 is white for EVERY
time and EVERY local gauge (`unobservable`, `initial_subset`, `H_any_gauge`).
After two steps this is an additive Rule150 reflection mode. Actual nonlinear
recombination disagrees: the k=1 recombined center is black at time7 while
the linear mode stays white (`actual_center_diverges`).

These backgrounds have NO left bound (`backgrounds_no_left_bound`). This is
not a counterexample for finite or left-bounded initial backgrounds, to the
open EdgeObservable conjecture, or to the Rule30 prize problem. Eventual
vacuum and gauge identities alone cannot establish the observer criterion.
`Front.mode_left_edge` retains a hypothesis the counterexample lacks: if
both actual backgrounds vanish below lo and the initial mode has left edge
lo, that mode keeps its left edge lo-t for every time and every local gauge.
It does not assert that this edge must affect the observation column.

All proofs are core Lean; no Mathlib or finite-horizon premise. The Boolean
identities and two concrete divergence controls use `decide +kernel`.
Proof and formalization: Troy Lowry with OpenAI Codex.
-/'''
text=text[:i]+intro+text[j:]
path=repo/'lean/Ruliology/CellularAutomata/Rule30DividedDifference.lean'
if path.exists():assert 'namespace Ruliology.CellularAutomata.Rule30DividedDifference' in path.read_text()
path.write_text(text,encoding='utf-8',newline='\n')
imports=repo/'lean/Ruliology.lean';s=imports.read_text(encoding='utf-8')
anchor='public import Ruliology.CellularAutomata.Rule30FiniteConfigs\n';assert s.count(anchor)==1
if 'public import Ruliology.CellularAutomata.Rule30DividedDifference\n' not in s:
    s=s.replace(anchor,anchor+'public import Ruliology.CellularAutomata.Rule30DividedDifference\n')
imports.write_text(s,encoding='utf-8',newline='\n')
readme=repo/'lean/README.md';s=readme.read_text(encoding='utf-8')
anchor='| Module | Added | What it proves | Headline theorems |\n|---|---|---|---|\n';assert s.count(anchor)>=1
row='| `Rule30DividedDifference` | 2026-10-25 | Exact quadratic recombination error, local-gauge identities and all-time actual-pair representation for frozen Rule30 difference fields. For every source separation k>=1 and every gauge, a finite auxiliary mode is invisible for all time in two infinite periodic backgrounds that become vacuum after two steps; initial support inclusion does not restore physicality. These backgrounds have no left bound, so this does not refute finite-start observability or a prize statement. For arbitrary actual backgrounds vanishing below lo, every gauged mode with left edge lo keeps edge lo-t. Contributed by Troy Lowry with OpenAI Codex. | `curvature`, `Front.actual_difference`, `unobservable`, `initial_subset`, `backgrounds_no_left_bound`, `Front.mode_left_edge` |\n'
if '`Rule30DividedDifference`' in s:
    assert sum(x.startswith('| `Rule30DividedDifference` |') for x in s.splitlines())==1
    s='\n'.join(row.rstrip('\n') if x.startswith('| `Rule30DividedDifference` |') else x for x in s.splitlines())+'\n'
else:s=s.replace(anchor,anchor+row,1)
readme.write_text(s,encoding='utf-8',newline='\n')
print(json.dumps({'catalog_source':str(path),'lines':len(text.splitlines()),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}))
