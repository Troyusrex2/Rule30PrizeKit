from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent;digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((root/'MANIFEST.json').read_text())
for name,expected in manifest.items():assert digest(root/name)==expected,name
meta=json.loads((root/'sources.json').read_text());count=0
for name,expected in meta['sources'].items():
 source=root/(name+'.lean');assert digest(source)==expected,name
 assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',source.read_bytes(),re.M)
 r=json.loads((root/'formal'/name/'report.json').read_text())
 assert digest(root/'formal'/name/'source.lean')==expected==r['source_sha256'] and r['passed']
 assert r['pin']=='5473ffd075f63c9d626e63b8455805d4831b39ca'
 assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
 c=r['checker'];assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms']
 assert all(h['ok'] for h in c['headlines']);count+=c['replay']['constants']
 g=json.loads((root/'evidence'/('replay-'+name+'.guard.json')).read_text())
 assert g['exit_code']==0 and g['guard_stop'] is None
for name,d in meta['dependencies'].items():
 assert digest(root/'dependencies'/(name+'.lean'))==d['source_sha256']
 r=json.loads((root/'dependency-receipts'/name/'report.json').read_text())
 assert r['source_sha256']==d['source_sha256'] and r['compiled_sha256']==d['compiled_sha256']
 assert r['checker']['verdict']=='pass' and r['checker']['replay']['ok']
assert count==165
print(json.dumps({'passed':True,'manifest_files':len(manifest),'sources':len(meta['sources']),'dependencies':len(meta['dependencies']),'declarations_replayed':count,'manifest_sha256':digest(root/'MANIFEST.json')}))
