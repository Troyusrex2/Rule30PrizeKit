"""Run activated Wolfram Engine locally, without cloud authentication."""
import importlib.util,json
from pathlib import Path
from core import HERE,REPO
from coupled_even_code_probe import decode

spec=importlib.util.spec_from_file_location('guard',REPO/'research/normalization-first-meeting/replay.py')
guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
engine=Path('C:/Program Files/Wolfram Research/Wolfram Engine/15.0/wolframscript.exe')
elapsed=guard.guarded([str(engine),'-file',str(HERE/'EvenSupportPhysicalControl.wl')],HERE,
                      HERE/'even-support-wolfram-control.log')
r=json.loads((HERE/'even-support-wolfram-control.json').read_text(encoding='utf-8'))
assert len(r['cases'])==32
for case in r['cases']:assert case['free_bits']==decode(case['even_input'],24)
out={'cases':32,'free_bits_per_case':24,'all_physical_controls_match':True,
     'seconds':elapsed,'proof_premise':False}
(HERE/'even-support-wolfram-comparison.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print(out,flush=True)
