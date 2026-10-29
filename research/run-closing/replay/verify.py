"""Replay the frozen research proof with Lean 4.35.0 and the official checker.
Usage: python verify.py --lean C:/path/to/lean.exe --out C:/new/empty/directory
No network, packages, compiled proof objects or credentials are required.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--lean',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
root=Path(__file__).resolve().parent.parent
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
hashes=json.loads((root/'SOURCE-HASHES.json').read_text())
for rel,h in hashes.items():assert sha(root/rel)==h,rel
version=subprocess.check_output([str(a.lean.resolve()),'--version'],text=True).strip()
assert version.startswith('Lean (version 4.35.0,'),version
assert sha(root/'replay/Check.lean')=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
out=a.out.resolve();out.mkdir(exist_ok=False);project=out/'project'
shutil.copytree(root/'replay/sources',project)
shutil.copyfile(root/'replay/Check.lean',project/'Check.lean')
env=dict(os.environ,PATH=str(a.lean.resolve().parent)+os.pathsep+os.environ.get('PATH',''),LEAN_NUM_THREADS='1')
env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
lean=a.lean.resolve();lake=lean.with_name('lake.exe' if lean.suffix=='.exe' else 'lake')
def run(args,log):
    with (out/log).open('wb') as f:r=subprocess.run(list(map(str,args)),cwd=project,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=180)
    if r.returncode:print((out/log).read_text(encoding='utf-8',errors='replace')[-6000:]);r.check_returncode()
start=time.monotonic();specs=json.loads((root/'replay/SPECS.json').read_text())
official=json.loads((root/'replay/OFFICIAL-INPUTS.json').read_text())
run([lake,'build',*specs],'build.log')
checks={}
for module,heads in specs.items():
    args=[lake,'env',lean,'--run',project/'Check.lean',module,'--claim','partial']
    for h in heads:args+=['--headline',h]
    log=module+'-check.log';run(args,log)
    c=json.loads(next(l for l in reversed((out/log).read_text(encoding='utf-8').splitlines()) if l.startswith('{')))
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms']
    assert all(h['ok'] and h['typeMatches'] for h in c['headlines']);checks[module]=c
result={'passed':True,'checks':checks,'fresh_sources':len(official['modules'])+len(specs),'reused_owned_objects':False,
        'lean_version':version,'lean_binary_sha256':sha(lean),
        'constants':sum(c['replay']['constants'] for c in checks.values()),
        'headlines':sum(len(c['headlines']) for c in checks.values()),
        'source_warnings':'warning:' in (out/'build.log').read_text(encoding='utf-8'),
        'seconds':time.monotonic()-start,'prize_solution':False}
(out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='checks'}))
