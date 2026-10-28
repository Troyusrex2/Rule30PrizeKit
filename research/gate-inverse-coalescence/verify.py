"""Fresh standalone source build and unchanged-checker replay; Python standard library only."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import subprocess

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--lean', type=Path)
parser.add_argument('--out', type=Path)
parser.add_argument('--audit-only', action='store_true')
args = parser.parse_args()
meta = json.loads((root/'INPUTS.json').read_text(encoding='utf-8'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for item in meta['files']:
    assert sha(root/item['path']) == item['sha256'], item['path']
if args.audit_only:
    print(json.dumps({'audit_passed': True, 'files_checked': len(meta['files'])}))
    raise SystemExit(0)
if not args.lean:
    parser.error('--lean /path/to/lean is required unless --audit-only is used')
lean = args.lean.resolve()
version = subprocess.run([str(lean),'--version'],capture_output=True,text=True,check=True).stdout.strip()
assert '4.35.0' in version, version
out = (args.out or root/'runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')).resolve()
out.mkdir(parents=True,exist_ok=False)
lib = out/'lib'
lib.mkdir()
env = dict(os.environ, LEAN_PATH=str(lib), LEAN_NUM_THREADS='1')
builds = []


def execute(command, cwd, log):
    with log.open('wb') as stream:
        p = subprocess.run(command,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
    if p.returncode:
        print(log.read_text(encoding='utf-8',errors='replace')[-6000:])
        p.check_returncode()


for dep in meta['dependencies']:
    rel = Path(*dep['module'].split('.'))
    target = lib/rel.with_suffix('.olean')
    target.parent.mkdir(parents=True,exist_ok=True)
    log = out/(dep['module']+'.build.log')
    execute([str(lean),'-o',str(target),str(rel.with_suffix('.lean'))],root/'sources',log)
    builds.append({'module':dep['module'],'object_sha256':sha(target),
                   'source_warnings':b'warning:' in log.read_bytes()})

results = []
for proof in meta['proofs']:
    module = proof['module']
    source = root/(module+'.lean')
    build = out/(module+'.build.log')
    execute([str(lean),'-o',str(lib/(module+'.olean')),str(source)],root,build)
    command = [str(lean),'--run',str(root/'Check.lean'),module,'--claim','partial']
    for h in proof['headlines']:
        command += ['--headline',h]
    check = out/(module+'.check.log')
    execute(command,root,check)
    report = json.loads(next(line for line in reversed(check.read_text(encoding='utf-8').splitlines()) if line.startswith('{')))
    assert report['verdict']=='pass' and report['replay']['ok'] and not report['newAxioms']
    assert all(h['ok'] and h['typeMatches'] for h in report['headlines'])
    types = out/(module+'.Types.lean')
    types.write_text('import '+module+'\n'+''.join('#check @'+h+'\n#print axioms '+h+'\n' for h in proof['headlines']),encoding='utf-8')
    execute([str(lean),str(types)],root,out/(module+'.Types.log'))
    warnings = b'warning:' in build.read_bytes()
    assert not warnings, 'Proof source warnings: '+module
    results.append({'module':module,'source_sha256':sha(source),
                    'object_sha256':sha(lib/(module+'.olean')),'checker':report,
                    'source_warnings':warnings})

result = {'passed':True,'lean_version':version,'official_pin':meta['official_pin'],
          'fresh_official_sources':len(builds),'fresh_proof_sources':len(results),
          'reused_objects':False,'builds':builds,'proofs':results,
          'checker_sha256':sha(root/'Check.lean')}
(out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':True,'fresh_sources':len(builds)+len(results),
                  'proofs':[{'module':p['module'],'constants':p['checker']['replay']['constants'],
                             'headlines':len(p['checker']['headlines'])} for p in results]}))
