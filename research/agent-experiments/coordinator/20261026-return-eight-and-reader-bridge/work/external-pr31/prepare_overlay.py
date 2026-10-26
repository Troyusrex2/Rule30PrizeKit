"""Freeze a private import overlay; the pinned reference remains read-only."""
from pathlib import Path
import json,hashlib,shutil
root=Path(__file__).resolve().parent
owner=Path.home()/'Rule30-offload';assert root.is_relative_to(owner)
ref=owner/'research/verifier9-20261026/project'
manifest=json.loads((root/'official-dependencies.json').read_bytes());copied=[];missing=[]
for module,item in manifest['modules'].items():
    source=ref/item['path'];assert hashlib.sha256(source.read_bytes()).hexdigest()==item['source_sha256']
    relative=Path(*module.split('.'));folder=ref/'.lake/build/lib/lean'/relative.parent
    files=list(folder.glob(relative.name+'.olean*'))+list(folder.glob(relative.name+'.ilean'))
    if not any(p.name==relative.name+'.olean' for p in files):
        missing.append(module)
        continue
    for p in files:
        target=root/'lib'/relative.parent/p.name;target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists():
            assert target.read_bytes()==p.read_bytes(),target
        else:
            shutil.copyfile(p,target)
        copied.append({'module':module,'artifact':str(target.relative_to(root)).replace('\\','/'),'sha256':hashlib.sha256(target.read_bytes()).hexdigest()})
(root/'overlay-receipt.json').write_text(json.dumps({'source_hashes_passed':True,'pin':manifest['pin'],'source_hashes_checked':len(manifest['modules']),'copied':copied,'missing_compiled_modules':missing,'reference_write':False},indent=2)+'\n',encoding='utf-8')
print(json.dumps({'official_sources_checked':len(manifest['modules']),'private_import_files':len(copied),'missing_compiled_modules':missing,'reference_write':False}))
