from pathlib import Path
root=Path(__file__).resolve().parent
repo=Path(r'D:\MWB\Rule30\spatial-lifting-catalog-20261025')
first=(root/'Rule30SpatialLiftingResearch.lean').read_text(encoding='utf-8')
first=first.split('namespace Rule30SpatialLiftingResearch\n',1)[1].rsplit('end Rule30SpatialLiftingResearch',1)[0]
second=(root/'Rule30SpatialPeriodResearch.lean').read_text(encoding='utf-8')
second=second.split('namespace Rule30SpatialPeriodResearch\n',1)[1].rsplit('end Rule30SpatialPeriodResearch',1)[0]
second=second.replace('open Rule30SpatialLiftingResearch\n','')
header='''module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# Uniform spatial period lifting in sideways Rule 30 reconstruction

Write a pair of consecutive cells as a state in `Fin 4`. The next spatial
state, driven by the cell on the next temporal row, is
`(a,b) ↦ (b, u XOR (b OR a))` (`step_encode`).

The two transfer maps generate 41 transformations. Of these, 37 occur
for words containing a white driver cell. Their closure and the identity
`F^5=F^3` are kernel checked. Induction on arbitrary words makes this a
statement for every block length, rather than a fixed-width certificate.

`stateAt_period` proves that a periodic driver with period p and a white
cell yields spatial period 2p after at most 3p steps, for any initial pair.
`recon_period_lift` connects this directly to the official `recon`: if row
t+1 has period p after depth D+1, and its period contains a white cell,
row t has period 2p after depth D+3p. Both p and D are unbounded.

The result permits successive period doublings. It does not bound all
spatial periods by 28, prove absorption, supply a density bound, or solve
Q01, CQ01 or a prize problem. The white-cell hypothesis is necessary:
the all-black driver transfer has a three-cycle.

Contributed by Troy Lowry with OpenAI Codex, 2026-10-25.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SpatialPeriodLifting
'''
source=header+first+second+'\nend Ruliology.CellularAutomata.Rule30SpatialPeriodLifting\n'
target=repo/'lean/Ruliology/CellularAutomata/Rule30SpatialPeriodLifting.lean'
assert not target.exists();target.write_text(source,encoding='utf-8',newline='\n')
p=repo/'lean/Ruliology.lean';s=p.read_text(encoding='utf-8');anchor='public import Ruliology.CellularAutomata.Rule30ZeroBoundary\n'
assert s.count(anchor)==1;p.write_text(s.replace(anchor,anchor+'public import Ruliology.CellularAutomata.Rule30SpatialPeriodLifting\n'),encoding='utf-8',newline='\n')
p=repo/'lean/README.md';s=p.read_text(encoding='utf-8');i=s.index('## Added in the kit');t=s.index('\n|---',i);end=s.index('\n',t+1)
row='\n| `Rule30SpatialPeriodLifting` | 2026-10-25 | Uniform sideways period lifting: if reconstructed row t+1 has spatial period p after D+1 and a white cell in that period, row t has period 2p after D+3p. A 37-transformation kernel check proves the arbitrary-block identity F^5=F^3; no density or prize solution is claimed. Contributed by Troy Lowry with OpenAI Codex. | `word_power`, `stateAt_period`, `recon_period_lift` |'
p.write_text(s[:end]+row+s[end:],encoding='utf-8',newline='\n')
old=(root.parent/'source-green-20261025T1610/check_catalog.py').read_text()
old=old.replace('dyadic-source-catalog-20261025','spatial-lifting-catalog-20261025').replace('Rule30RunBoundarySources','Rule30SpatialPeriodLifting').replace("['selected_event_iff_outer','source_physical','rule90_source_identity']","['word_power','stateAt_period','recon_period_lift']")
(root/'check_catalog.py').write_text(old,encoding='utf-8')
print(target)
