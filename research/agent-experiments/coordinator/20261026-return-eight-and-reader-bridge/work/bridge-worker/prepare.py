from pathlib import Path
import hashlib,shutil,json
root=Path(__file__).parent;base=root.parent
deps={'Rule30CommonPastResearch':base/'collision-bridge-20261026T0540/Rule30CommonPastResearch.lean',
      'Rule30ColumnReaderResearch':base/'collision-bridge-20261026T0540/Rule30ColumnReaderResearch.lean'}
for n in ['CedarSafetySoundness','CedarSafetySemantics','CedarSafetyBridge']:
    deps[n]=base/'short-extension-root-review-20261026T1840'/(n+'.lean')
for n,p in deps.items():shutil.copyfile(p,root/(n+'.lean'))
deps['PrizeSafetyBridge']=root/'PrizeSafetyBridge.lean'
meta={n:{'original':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for n,p in deps.items()}
(root/'sources.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({'sources':len(meta),'fresh_dependency_builds':5}))
