"""Port the two checked research sources into one core catalog module."""
from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parent
ref=Path(r'D:\MWB\Rule30\current-reference-009005-20261025')
repo=Path(r'D:\MWB\Rule30\common-gauge-catalog-20261025')
branch='contribution/common-gauge-20261025';pin='0090056412733accaa27643d3cbbf982104f2251'
if not repo.exists():
    subprocess.run(['git','worktree','add','-b',branch,str(repo),pin],cwd=ref,check=True)
else:
    assert subprocess.check_output(['git','branch','--show-current'],cwd=repo,text=True).strip()==branch
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==pin
ns='Ruliology.CellularAutomata.Rule30CommonGauge'
vac=(root/'Rule30VacuumGaugeResearch.lean').read_text(encoding='utf-8')
vac=vac.replace('Rule30VacuumGaugeResearch',ns)
vac=vac.replace('public import Ruliology.CellularAutomata.Rule30Prize\n',
                'public import Ruliology.CellularAutomata.Rule30Prize\npublic import Ruliology.CellularAutomata.Rule30Diagonals\n')
vac=vac.replace('No claim of a canonical center observer or Prize Problem 1 is made.',
'''The right-wedge section applies it uniformly to every actual canonical age
pair U>V. Beyond the younger row's right front, any supported common field
equals its initial older-right-edge bit times the older canonical row.
The finite-horizon version has a distance-dependent bound. The overlap
containing the center and the left edge remains unresolved.
Proof and formalization: Troy Lowry with OpenAI Codex.''')
assert vac.endswith('end '+ns+'\n')
vac=vac[:-len('end '+ns+'\n')]
wedge=(root/'Rule30RightWedgeResearch.lean').read_text(encoding='utf-8')
marker='@[expose] public section\nnamespace Rule30RightWedgeResearch\n'
assert wedge.count(marker)==1
wedge=wedge.split(marker)[1]
assert wedge.endswith('end Rule30RightWedgeResearch\n')
wedge=wedge[:-len('end Rule30RightWedgeResearch\n')]
wedge=wedge.replace('open Ruliology.CellularAutomata\n','')
wedge=wedge.replace('open Rule30Jen (cell rule)','open _root_.Ruliology.CellularAutomata.Rule30Jen (cell)')
wedge=wedge.replace('open Rule30VacuumGaugeResearch\n','')
text=vac+'\nnamespace RightWedge\n'+wedge+'end RightWedge\nend '+ns+'\n'
path=repo/'lean/Ruliology/CellularAutomata/Rule30CommonGauge.lean'
path.write_text(text,encoding='utf-8',newline='\n')
imports=repo/'lean/Ruliology.lean';s=imports.read_text(encoding='utf-8')
anchor='public import Ruliology.CellularAutomata.Rule30Prize\n';assert s.count(anchor)==1
if 'public import '+ns+'\n' not in s:
    imports.write_text(s.replace(anchor,anchor+'public import '+ns+'\n'),encoding='utf-8',newline='\n')
readme=repo/'lean/README.md';s=readme.read_text(encoding='utf-8')
anchor='| Module | Added | What it proves | Headline theorems |\n|---|---|---|---|\n';assert anchor in s
row='| `Rule30CommonGauge` | 2026-10-25 | Auxiliary divided-difference fields satisfying both local gauges: an asymmetric gap theorem with a distance-dependent finite horizon; exact zero-background classification for every initial subset field; and, for every canonical U>V, phase coherence beyond the younger row\'s right front. The field is not assumed to be a physical history. Adapts the catalog\'s XOR-rigidity gap argument; neither the center observer nor a prize solution is claimed. Contributed by Troy Lowry with OpenAI Codex. | `HalfLine.distant_good_right_black_through`, `HalfLine.common_mode_classification`, `RightWedge.right_wedge_phase_through`, `RightWedge.right_wedge_phase_subset` |\n'
assert '`Rule30CommonGauge`' not in s
readme.write_text(s.replace(anchor,anchor+row,1),encoding='utf-8',newline='\n')
out={'branch':branch,'base':pin,'catalog_path':str(path),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
     'lines':len(text.splitlines()),'no_Mathlib':True,'same_math_as_research_sources':True,'full_problem_solved':False}
(root/'catalog-preparation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
