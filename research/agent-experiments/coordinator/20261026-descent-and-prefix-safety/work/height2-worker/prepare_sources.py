from pathlib import Path
import json,hashlib,shutil,subprocess
root=Path(__file__).resolve().parent;base=root.parent
sources=json.loads((base/'height1-transfer-20261026T2007/sources.json').read_bytes())
copied={}
for module,item in sources['dependencies'].items():
    path=base/item['phase']/(module+'.lean');raw=path.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==item['source_sha256'],module
    (root/(module+'.lean')).write_bytes(raw);copied[module]={'source':str(path),'sha256':item['source_sha256']}
for module in ['HeightOneLogic','HeightOneSemantics']:
    path=base/'height1-transfer-20261026T2007'/(module+'.lean');raw=path.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==sources['sources'][module]
    (root/(module+'.lean')).write_bytes(raw);copied[module]={'source':str(path),'sha256':sources['sources'][module]}
(root/'dependencies.json').write_text(json.dumps(copied,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'exact_dependencies':len(copied)}))
