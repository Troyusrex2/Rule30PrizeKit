"""Compile exactly one pending pinned official dependency into the private overlay."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
ref=owner/'research/verifier9-20261026/project';lib=root/'lib'
key=sys.argv[1];assert key.isidentifier()
module=json.loads((root/'split-plan.json').read_bytes())[key]
manifest=json.loads((root/'official-dependencies.json').read_bytes())
item=manifest['modules'][module];raw=(ref/item['path']).read_bytes()
assert hashlib.sha256(raw).hexdigest()==item['source_sha256']
for dep in re.findall(r'^(?:public )?import\s+([\w.]+)',raw.decode('utf-8'),re.M):
    if dep.startswith('Ruliology.'):
        assert (lib/Path(*dep.split('.')).with_suffix('.olean')).exists(),dep
local=root/'official-source'/Path(*module.split('.')).with_suffix('.lean');local.parent.mkdir(parents=True,exist_ok=True);local.write_bytes(raw)
compiled=lib/Path(*module.split('.')).with_suffix('.olean');compiled.parent.mkdir(parents=True,exist_ok=True)
out=root/'official-split';out.mkdir(exist_ok=True)
env=dict(os.environ,LEAN_PATH=str(lib)+';'+str(ref/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
start=time.monotonic()
with (out/(key+'.log')).open('wb') as stream:
    proc=subprocess.run([str(owner/'_cache/payload/toolchain/bin/lean.exe'),'-o',str(compiled),str(local)],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
if proc.returncode:
    print((out/(key+'.log')).read_text(encoding='utf-8',errors='replace')[-4000:]);proc.check_returncode()
receipt={'passed':True,'module':module,'source_sha256':item['source_sha256'],'compiled_sha256':hashlib.sha256(compiled.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'reference_write':False}
(out/(key+'.json')).write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps(receipt))
