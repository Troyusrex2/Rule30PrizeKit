"""Fresh core-Lean Lake build and unchanged full checker; no external packages."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,subprocess,time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lean',default='lean',help='Lean 4.35.0 toolchain executable')
parser.add_argument('--lake',default=None,help='Lake executable; default is beside the chosen Lean')
parser.add_argument('--run-name',default=None)
parser.add_argument('--audit-only',action='store_true',help='Check archive hashes only; do not invoke Lean or Lake')
args=parser.parse_args()
root=Path(__file__).resolve().parent
meta=json.loads((root/'SOURCES.json').read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((root/'MANIFEST.json').read_text(encoding='utf-8'))
for item in manifest['files']:
    relative=Path(item['path'])
    assert not relative.is_absolute() and '..' not in relative.parts
    assert sha(root/relative)==item['sha256'],relative
assert sha(root/'Check.lean')==meta['checker_sha256']
for module,digest in meta['sources'].items():
    source=root/Path(*module.split('.')).with_suffix('.lean')
    assert sha(source)==digest,module
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',source.read_bytes(),re.M),module
assert len(meta['sources'])==21 and len(meta['official_sources'])==14
for name,digest in meta['config_hashes'].items():assert sha(root/name)==digest
if args.audit_only:
    print(json.dumps({'archive_hashes_passed':True,'sources':21,'lean_invoked':False}))
    raise SystemExit(0)
def executable(value):
    resolved=shutil.which(value)
    assert resolved is not None,'Executable not found: '+value
    return Path(resolved).resolve()
lean=executable(args.lean)
lake=executable(args.lake) if args.lake else lean.with_name('lake'+lean.suffix)
assert lake.is_file(),'Pass --lake pointing to the matching toolchain executable'
version=subprocess.check_output([str(lean),'--version'],text=True).strip()
assert 'version 4.35.0,' in version,version
run_name=args.run_name or datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
assert re.fullmatch(r'[A-Za-z0-9_-]+',run_name)
run=root/'runs'/run_name
project=run/'project';project.mkdir(parents=True,exist_ok=False)
evidence=run/'evidence';evidence.mkdir()
for module in meta['order']:
    rel=Path(*module.split('.')).with_suffix('.lean')
    target=project/rel;target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes((root/rel).read_bytes())
for name in ['Check.lean','lakefile.toml','lean-toolchain']:(project/name).write_bytes((root/name).read_bytes())
assert not (project/'.lake').exists()
env=dict(os.environ)
env.pop('LEAN_PATH',None)
env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
env['LEAN_NUM_THREADS']='1'
def execute(command,log):
    start=time.monotonic()
    with log.open('wb') as stream:
        result=subprocess.run(command,cwd=project,env=env,stdout=stream,stderr=subprocess.STDOUT)
    if result.returncode:
        print(log.read_text(encoding='utf-8',errors='replace')[-12000:])
        result.check_returncode()
    return time.monotonic()-start
build_seconds=execute([str(lake),'build',*meta['build_targets']],evidence/'lake-build.log')
checks=[]
for module,heads in meta['heads'].items():
    cmd=[str(lake),'env',str(lean),'--run','Check.lean',module,'--claim','partial']
    for head in heads:cmd+=['--headline',head]
    log=evidence/(module+'.check.log')
    seconds=execute(cmd,log)
    verdict=json.loads(next(s for s in reversed(log.read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
    assert verdict['verdict']=='pass' and verdict['replay']['ok'] and not verdict['newAxioms']
    assert verdict['replay']['constants']==meta['expected_constants'][module]
    assert [h['name'] for h in verdict['headlines']]==heads
    assert all(h['ok'] and h['typeMatches'] for h in verdict['headlines'])
    checks.append({'module':module,'seconds':seconds,'result':verdict})
types=''.join('import '+m+'\n' for m in meta['heads'])+''.join(
    '#check @'+h+'\n#print axioms '+h+'\n' for heads in meta['heads'].values() for h in heads)
(project/'CheckNewTypes.lean').write_text(types,encoding='utf-8',newline='\n')
execute([str(lake),'env',str(lean),'CheckNewTypes.lean'],evidence/'Types.log')
normalize=lambda s:re.sub(r'\s+','',s)
assert normalize((evidence/'Types.log').read_text(encoding='utf-8'))==normalize(
    (root/'evidence/root-full-lake/Types.log').read_text(encoding='utf-8')),'Printed types/axioms differ from audited receipt'
objects={}
for module,digest in meta['sources'].items():
    rel=Path(*module.split('.')).with_suffix('.lean')
    assert sha(project/rel)==digest
    objects[module]=sha(project/'.lake/build/lib/lean'/rel.with_suffix('.olean'))
assert sha(project/'Check.lean')==meta['checker_sha256']
out={'passed':True,'official_pin':meta['official_pin'],'fresh_sources':21,'reference_objects_used':False,
    'external_LEAN_PATH_cleared':True,'core_only':True,'build_seconds':build_seconds,
    'source_hashes':meta['sources'],'object_hashes':objects,'checks':checks,
    'constants':sum(c['result']['replay']['constants'] for c in checks),
    'headlines':sum(map(len,meta['heads'].values())),'exact_printed_types_and_axioms_match':True,
    'checker_sha256':meta['checker_sha256'],'lean_version':version,'lean_binary_sha256':sha(lean),
    'source_warning':b'warning:' in (evidence/'lake-build.log').read_bytes()}
(evidence/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':True,'fresh_sources':21,'constants':out['constants'],'headlines':out['headlines']}))
