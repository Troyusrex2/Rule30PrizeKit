"""Rebuild the canonical catalog modules with Lake, without Mathlib or reused objects."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import time

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--archive',type=Path,default=root.parent)
parser.add_argument('--lean',type=Path)
parser.add_argument('--lake',type=Path)
parser.add_argument('--out',type=Path)
parser.add_argument('--audit-only',action='store_true')
args = parser.parse_args()
archive = args.archive.resolve()
meta = json.loads((root/'INPUTS.json').read_text(encoding='utf-8'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
sources = []
for item in meta['source_files']:
    rel = Path(item['path']).relative_to('lean')
    source = root/'sources'/rel
    if not source.exists():
        source = archive/'sources'/rel
    assert sha(source)==item['sha256'],str(source)
    sources.append((item,source))
assert sha(archive/'Check.lean')==meta['checker_sha256']
if args.audit_only:
    print(json.dumps({'audit_passed':True,'sources':len(sources)}))
    raise SystemExit(0)
if not args.lean or not args.lake:
    parser.error('--lean and --lake are required')
lean,lake = args.lean.resolve(),args.lake.resolve()
version = subprocess.run([str(lean),'--version'],capture_output=True,text=True,check=True).stdout.strip()
assert '4.35.0' in version
out = (args.out or root/'runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')).resolve()
out.mkdir(parents=True,exist_ok=False)
project = out/'project'
project.mkdir()
for item,source in sources:
    rel = Path(item['path']).relative_to('lean')
    target = project/rel
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,target)
shutil.copyfile(archive/'Check.lean',project/'Check.lean')
(project/'lakefile.toml').write_text('name = "gateinversecanonical"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Ruliology"\n',encoding='utf-8')
(project/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n',encoding='utf-8')
env = dict(os.environ,PATH=str(lean.parent)+os.pathsep+os.environ.get('PATH',''),LEAN_NUM_THREADS='1')
env.pop('LEAN_PATH',None)
env.pop('LEAN_SRC_PATH',None)


def execute(command,log):
    with (out/log).open('wb') as stream:
        p = subprocess.run(command,cwd=project,env=env,stdout=stream,stderr=subprocess.STDOUT)
    if p.returncode:
        print((out/log).read_text(encoding='utf-8',errors='replace')[-6000:])
        p.check_returncode()


start = time.monotonic()
reports = []
for proof in meta['proofs']:
    module = proof['module']
    execute([str(lake),'build',module],module+'.build.log')
    command = [str(lake),'env',str(lean),'--run',str(project/'Check.lean'),module,'--claim','partial']
    for h in proof['headlines']:
        command += ['--headline',h]
    execute(command,module+'.check.log')
    report = json.loads(next(line for line in reversed((out/(module+'.check.log')).read_text(encoding='utf-8').splitlines()) if line.startswith('{')))
    assert report['verdict']=='pass' and report['replay']['ok'] and not report['newAxioms']
    assert all(h['ok'] and h['typeMatches'] for h in report['headlines'])
    types = out/(module+'.Types.lean')
    types.write_text('import '+module+'\n'+''.join('#check @'+h+'\n#print axioms '+h+'\n' for h in proof['headlines']),encoding='utf-8')
    execute([str(lake),'env',str(lean),str(types)],module+'.Types.log')
    reports.append({'module':module,'checker':report,
                    'build_warnings':b'warning:' in (out/(module+'.build.log')).read_bytes()})
smoke = out/'ThreeImports.lean'
smoke.write_text(''.join('import '+p['module']+'\n' for p in meta['proofs']),encoding='utf-8')
execute([str(lake),'env',str(lean),str(smoke)],'ThreeImports.log')
result = {'passed':True,'fresh_source_closure':len(sources),'reused_objects':False,
          'official_pin':meta['official_pin'],'checker_sha256':meta['checker_sha256'],
          'lean_version':version,'proofs':reports,'three_import_smoke_passed':True,
          'whole_catalog_build':False,'seconds':time.monotonic()-start}
(out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':True,'fresh_sources':len(sources),'proofs':[
    {'module':p['module'],'constants':p['checker']['replay']['constants'],
     'heads':len(p['checker']['headlines'])} for p in reports]}))
