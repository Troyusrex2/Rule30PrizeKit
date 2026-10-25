"""Consolidate the original 256-segment data for a same-host compiler comparison."""
import hashlib,json,re
from core import HERE,BASE

source=BASE/'stripe13-completion-catalog/lean/Ruliology/CellularAutomata/Rule30Certificates'
text='''module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! Monolithic baseline of the original 256 tail-13 certificate segments.
For compiler comparison only; this is the already checked earlier proof. -/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 0

'''
names=[]
for i in range(32):
    path=source/f'StripeTail13Completion{i:02d}.lean';raw=path.read_text(encoding='utf-8')
    block=raw[raw.index('namespace Ruliology.CellularAutomata.Rule30Tail13Completion'):]
    text+=block+'\n';names+=re.findall(r'^(?:theorem|def|structure|abbrev)\s+(\w+)',block,re.M)
assert len(names)==len(set(names))
path=HERE/'Rule30Tail13MergedBaseline.lean';path.write_text(text,encoding='utf-8',newline='\n')
info={'original_pr_head':'7de67a48c2f9e8029ebec4346d5b4291b4035869','source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
      'merged_modules':32,'explicit_declarations':len(names),'normal_compile_only_benchmark':True}
(HERE/'tail13-baseline-manifest.json').write_text(json.dumps(info,indent=2)+'\n',encoding='utf-8',newline='\n')
print(info,flush=True)
