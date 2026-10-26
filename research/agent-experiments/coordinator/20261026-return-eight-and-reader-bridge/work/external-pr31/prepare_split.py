"""Retain completed exact pinned compiles; plan separate guarded remaining jobs."""
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
ref=owner/'research/verifier9-20261026/project';lib=root/'lib'
manifest=json.loads((root/'official-dependencies.json').read_bytes())
overlay=json.loads((root/'overlay-receipt.json').read_bytes())
guard=json.loads((root/'evidence/build_dependencies.guard.json').read_bytes())
assert guard['guard_stop']=='wall_time'
done=re.findall(r'^(Ruliology\.[\w.]+): compiled\.$',(root/'evidence/build_dependencies.log').read_text(encoding='utf-8'),re.M)
receipts=[]
for module in done:
    item=manifest['modules'][module];raw=(ref/item['path']).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==item['source_sha256']
    artifact=lib/Path(*module.split('.')).with_suffix('.olean');assert artifact.exists()
    assert (root/'official-source'/Path(*module.split('.')).with_suffix('.lean')).read_bytes()==raw
    receipts.append({'module':module,'source_sha256':item['source_sha256'],'compiled_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest(),'completion_evidence':'explicit successful subprocess return followed by flushed compiled line in aggregate log'})
missing=set(overlay['missing_compiled_modules'])-set(done);ordered=[];seen=set()
def visit(module):
    if module not in missing or module in seen:return
    seen.add(module)
    raw=(ref/manifest['modules'][module]['path']).read_bytes()
    for dep in re.findall(r'^(?:public )?import\s+([\w.]+)',raw.decode('utf-8'),re.M):visit(dep)
    ordered.append(module)
for module in sorted(missing):visit(module)
plan={m.removeprefix('Ruliology.CellularAutomata.').replace('.','_'):m for m in ordered}
(root/'split-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
(root/'aggregate-completed-receipt.json').write_text(json.dumps({'passed_completed_modules':True,'completed':receipts,'original_guard_stop':'wall_time','original_job_overall_passed':False},indent=2)+'\n',encoding='utf-8')
guardraw=(root/'guard.py').read_text(encoding='utf-8').replace("['replay','replay_with_reference_imports']","['replay','replay_with_reference_imports','build_dependency']")
(root/'guard_split.py').write_text(guardraw,encoding='utf-8')
print(json.dumps({'completed':len(done),'pending':plan}))
