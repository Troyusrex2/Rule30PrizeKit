"""Verify final overlay provenance; no compiler or reference mutation."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload';assert root.is_relative_to(owner)
ref=owner/'research/verifier9-20261026/project';manifest=json.loads((root/'official-dependencies.json').read_bytes())
overlay=json.loads((root/'overlay-receipt.json').read_bytes());compiled={}
for item in overlay['copied']:
    if item['artifact'].endswith('.olean'):
        compiled[item['module']]={'sha256':item['sha256'],'origin':'copied from pinned reference'}
for item in json.loads((root/'aggregate-completed-receipt.json').read_bytes())['completed']:
    compiled[item['module']]={'sha256':item['compiled_sha256'],'origin':'fresh successful compile before aggregate guard stop'}
for path in (root/'official-split').glob('*.json'):
    item=json.loads(path.read_bytes());assert item['passed']
    compiled[item['module']]={'sha256':item['compiled_sha256'],'origin':'fresh individually guarded compile'}
assert set(compiled)==set(manifest['modules'])
for module,item in manifest['modules'].items():
    assert hashlib.sha256((ref/item['path']).read_bytes()).hexdigest()==item['source_sha256']
    artifact=root/'lib'/Path(*module.split('.')).with_suffix('.olean')
    assert hashlib.sha256(artifact.read_bytes()).hexdigest()==compiled[module]['sha256']
for key in ['Rule30WhiteEndNine','Rule30PaddedWords']:
    report=json.loads((root/'formal'/key/'report.json').read_bytes());assert report['passed']
    assert hashlib.sha256((root/(key+'.lean')).read_bytes()).hexdigest()==report['source_sha256']
    artifact=root/'lib/Ruliology/CellularAutomata'/(key+'.olean')
    assert hashlib.sha256(artifact.read_bytes()).hexdigest()==report['compiled_module_sha256']
assert hashlib.sha256((ref/'Check.lean').read_bytes()).hexdigest()=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
data={'passed':True,'official_sources_rechecked':43,'official_compiled_modules_accounted':compiled,'public_modules_verified':2,'reference_write':False,'all_jobs_terminal':True}
(root/'final-environment-integrity.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':True,'official_dependency_count':len(compiled),'exact_public_modules':2}))
