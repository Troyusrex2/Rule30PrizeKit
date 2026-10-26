from pathlib import Path
import hashlib,json,shutil
root=Path(__file__).parent;base=root.parent
sealed=Path('D:/MWB/Rule30/agent-inbox/r30-codex-cedar-d3-20261026-0704c91b-v05')
assert hashlib.sha256((sealed/'MANIFEST.json').read_bytes()).hexdigest()=='69b76bbf7f35176f56f9d952d13949ba3eb5364977b353f95bb07d5020f9d334'
manifest=json.loads((sealed/'MANIFEST.json').read_text())
assert len(manifest)==460
for name,digest in manifest.items():assert hashlib.sha256((sealed/name).read_bytes()).hexdigest()==digest,name
deps={}
for phase,names in {
 'height-converse-review-20261026T1854':['RootEventHeight'],
 'short-extension-root-review-20261026T1840':['CedarSafetySoundness','CedarSafetySemantics','CedarSafetyBridge','CedarWhiteTransport','RootShortExtensionCore'],
 'tc-cylinder-root-review-20261026T1916':['CedarNo11011'],
 'return8-bridge-review-20261026T1942':['Rule30CommonPastResearch']}.items():
 for name in names:
  p=base/phase/(name+'.lean');r=json.loads((base/phase/'formal'/name/'report.json').read_text())
  assert r['checker']['verdict']=='pass' and hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
  deps[name]={'phase':phase,'source_sha256':r['source_sha256'],'compiled_sha256':r['compiled_sha256']}
  dest=root/'dependencies';dest.mkdir(exist_ok=True);shutil.copyfile(p,dest/p.name)
  receipt=root/'dependency-receipts'/name;receipt.mkdir(parents=True,exist_ok=True)
  shutil.copyfile(base/phase/'formal'/name/'report.json',receipt/'report.json')
sources={p.stem:hashlib.sha256(p.read_bytes()).hexdigest() for p in root.glob('*.lean')}
(root/'sources.json').write_text(json.dumps({'sources':sources,'dependencies':deps,'sealed_v05_hashes_checked':460},indent=2)+'\n')
shutil.copyfile(base/'prize-bridge-audit-20261026T1920/guard.py',root/'guard.py')
print(json.dumps({'sealed_v05_hashes':460,'dependencies':len(deps),'sources':list(sources)}))
