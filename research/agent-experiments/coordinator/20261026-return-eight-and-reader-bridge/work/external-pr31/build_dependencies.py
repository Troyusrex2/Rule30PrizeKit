"""Compile only missing pinned dependencies into the owned overlay."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
ref=owner/'research/verifier9-20261026/project';lib=root/'lib'
lean=owner/'_cache/payload/toolchain/bin/lean.exe'
manifest=json.loads((root/'official-dependencies.json').read_bytes())
overlay=json.loads((root/'overlay-receipt.json').read_bytes())
missing=set(overlay['missing_compiled_modules']);done=set();receipt=[]
env=dict(os.environ,LEAN_PATH=str(lib)+';'+str(ref/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
def build(module):
    if module in done or module not in missing:return
    item=manifest['modules'][module];source=ref/item['path'];raw=source.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==item['source_sha256']
    for dep in re.findall(r'^(?:public )?import\s+([\w.]+)',raw.decode('utf-8'),re.M):build(dep)
    local=root/'official-source'/Path(*module.split('.')).with_suffix('.lean')
    local.parent.mkdir(parents=True,exist_ok=True);local.write_bytes(raw)
    compiled=lib/Path(*module.split('.')).with_suffix('.olean');compiled.parent.mkdir(parents=True,exist_ok=True)
    log=root/'official-build'/Path(module+'.log');log.parent.mkdir(exist_ok=True)
    start=time.monotonic()
    with log.open('wb') as stream:
        proc=subprocess.run([str(lean),'-o',str(compiled),str(local)],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
    if proc.returncode:
        print(log.read_text(encoding='utf-8',errors='replace')[-4000:]);proc.check_returncode()
    receipt.append({'module':module,'source_sha256':item['source_sha256'],'compiled_sha256':hashlib.sha256(compiled.read_bytes()).hexdigest(),'seconds':time.monotonic()-start})
    done.add(module);print(module+': compiled.',flush=True)
for module in sorted(missing):build(module)
(root/'dependency-build-receipt.json').write_text(json.dumps({'passed':True,'pin':manifest['pin'],'reference_write':False,'compiled':receipt},indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':True,'compiled_count':len(receipt)}))
