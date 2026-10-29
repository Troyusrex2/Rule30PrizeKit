"""Fresh twelve-source build and unchanged-checker replay of all four PR modules."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time
arg=argparse.ArgumentParser();arg.add_argument('--lean',type=Path,required=True);arg.add_argument('--out',type=Path,required=True);a=arg.parse_args()
root=Path(__file__).resolve().parent;out=a.out.resolve();out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(a.lean)=='ec7a472d1c12a09b0c0c718f7427c2be527b3f5f07810fdbe076c2507c7a91ea'
assert sha(root/'Check.lean')=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
meta=json.loads((root/'INPUTS.json').read_text())
for f in meta['files']:assert sha(root/f['path'])==f['sha256']
project=out/'project';project.mkdir();shutil.copytree(root/'sources',project/'lean');shutil.copyfile(root/'Check.lean',project/'Check.lean')
(project/'lean/lakefile.toml').write_text('name = "gatetail"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Ruliology"\n')
env=dict(os.environ,PATH=str(a.lean.parent)+os.pathsep+os.environ.get('PATH',''),LEAN_NUM_THREADS='1');env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
lake=a.lean.parent/'lake.exe'
def run(args,name):
    with (out/name).open('wb') as log:r=subprocess.run(args,cwd=project/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
    if r.returncode:print((out/name).read_text(encoding='utf-8',errors='replace')[-7000:]);r.check_returncode()
start=time.monotonic();proofs=meta['proofs']
run([str(lake),'build',*[p['module'] for p in proofs]],'build.log')
reports=[]
for proof in proofs:
    module=proof['module'];label=module.split('.')[-1];heads=proof['headlines']
    cmd=[str(lake),'env',str(a.lean),'--run',str(project/'Check.lean'),module,'--claim','partial']
    for h in heads:cmd+=['--headline',h]
    run(cmd,label+'.check.log')
    c=json.loads(next(s for s in reversed((out/(label+'.check.log')).read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    types=out/(label+'.Types.lean');types.write_text('import '+module+'\n'+''.join('#check @'+h+'\n#print axioms '+h+'\n' for h in heads),encoding='utf-8')
    run([str(lake),'env',str(a.lean),str(types)],label+'.Types.log')
    reports.append({'module':module,'checker':c})
smoke=out/'FourImports.lean';smoke.write_text(''.join('import '+p['module']+'\n' for p in proofs),encoding='utf-8')
run([str(lake),'env',str(a.lean),str(smoke)],'FourImports.log')
for f in meta['files']:assert sha(root/f['path'])==f['sha256']
constants=sum(p['checker']['replay']['constants'] for p in reports);headlines=sum(len(p['checker']['headlines']) for p in reports)
assert constants==452 and headlines==39
r={'passed':True,'official_pin':meta['pin'],'fresh_source_modules':12,'proof_modules':4,'reused_objects':False,'whole_catalog_build':False,'reports':reports,'source_files':meta['files'],'source_warnings':b'warning:' in (out/'build.log').read_bytes(),'four_import_smoke_passed':True,'total_constants':constants,'total_headlines':headlines,'seconds':time.monotonic()-start}
(out/'RESULT.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ['reports','source_files']}))
