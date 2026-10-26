from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parent;repo=Path(r'D:\MWB\Rule30\common-gauge-catalog-20261025')
ns='Ruliology.CellularAutomata.Rule30CommonGauge'
parent='24fe825edf60abbad7d7373bfbfca0af68cf0f31'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==parent
path=repo/'lean/Ruliology/CellularAutomata/Rule30CommonGauge.lean'
base=subprocess.check_output(['git','show',parent+':lean/Ruliology/CellularAutomata/Rule30CommonGauge.lean'],cwd=repo).decode('utf-8')
assert hashlib.sha256(base.encode('utf-8')).hexdigest()=='748cc6a15913ab9362616b52c7c3890b4f5e3be9ef3dcc5477cbac5c53b9b80a'
research=(root/'Rule30BandEscapeResearch.lean').read_text(encoding='utf-8')
marker='namespace Rule30BandEscapeResearch\n';assert research.count(marker)==1
body=research.split(marker)[1];assert body.endswith('end Rule30BandEscapeResearch\n')
body=body[:-len('end Rule30BandEscapeResearch\n')]
body=body.replace('open Ruliology.CellularAutomata\n','').replace('open Rule30Diagonals (R R_periodic)',
     'open _root_.Ruliology.CellularAutomata.Rule30Diagonals (R R_periodic)')
assert base.endswith('end '+ns+'\n')
base=base[:-len('end '+ns+'\n')]
base=base.replace('containing the center and the left edge remains unresolved.',
'''containing the center and the left edge remains unresolved.
The BandEscape section proves that every nonzero field over a canonical
older background visits arbitrarily large right-edge depths after every
time. It uses dyadic returns and a backward peeling argument, without W
or an evolution hypothesis for the second coefficient background. This
does not force a visit to the moving center depth.''')
text=base+'\nnamespace BandEscape\n'+body+'\n'+(root/'band-ordinary.fragment.lean').read_text(encoding='utf-8')+'\nend BandEscape\nend '+ns+'\n'
path.write_text(text,encoding='utf-8',newline='\n')
readme=repo/'lean/README.md';lines=readme.read_text(encoding='utf-8').splitlines()
row='| `Rule30CommonGauge` | 2026-10-25 | Auxiliary divided-difference fields: exact zero-background common-mode classification and a distance-dependent gap theorem; phase coherence beyond the younger right front for every canonical age pair; and unbounded right-depth escape for every nonzero field over an older canonical background, even without W or second-background evolution. Includes ordinary-coordinate and finite-reset-window forms. Adapts XOR-rigidity gaps and dyadic returns; no moving-center observer or prize solution is claimed. Contributed by Troy Lowry with OpenAI Codex. | `HalfLine.common_mode_classification`, `RightWedge.right_wedge_phase_subset`, `BandEscape.escapes_near_reset`, `BandEscape.arbitrarily_deep_after_any_time`, `BandEscape.Ordinary.arbitrarily_far_behind_front` |'
assert sum(s.startswith('| `Rule30CommonGauge` |') for s in lines)==1
lines=[row if s.startswith('| `Rule30CommonGauge` |') else s for s in lines]
readme.write_text('\n'.join(lines)+'\n',encoding='utf-8',newline='\n')
(root/'catalog-preparation.json').write_text(json.dumps({'parent':parent,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
 'lines':len(text.splitlines()),'no_Mathlib':True,'full_problem_solved':False},indent=2)+'\n')
print('Catalog extension prepared; validation still required.')
