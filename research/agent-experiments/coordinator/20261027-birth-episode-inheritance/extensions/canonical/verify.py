"""Fresh canonical seven-source verification, using the parent archive's six official sources."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,subprocess,time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--archive',type=Path,default=None,help='Parent archive root; default ../../ from this extension')
parser.add_argument('--lean',default='lean',help='Lean 4.35.0 executable')
parser.add_argument('--lake',default=None,help='Matching Lake executable; default beside Lean')
parser.add_argument('--run-name',default=None)
parser.add_argument('--audit-only',action='store_true')
args=parser.parse_args()
root=Path(__file__).resolve().parent
archive=args.archive.resolve() if args.archive else root.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
meta=json.loads((root/'SOURCES.json').read_text(encoding='utf-8'))
manifest=json.loads((root/'MANIFEST.json').read_text(encoding='utf-8'))
for item in manifest['files']:
    rel=Path(item['path']);assert not rel.is_absolute() and '..' not in rel.parts
    assert sha(root/rel)==item['sha256'],rel
assert sha(archive/'SOURCES.json')==meta['parent_sources_metadata_sha256']
parent=json.loads((archive/'SOURCES.json').read_text(encoding='utf-8'))
assert parent['official_pin']==meta['official_pin']
assert sha(archive/'Check.lean')==meta['checker_sha256']
def source(module):
    rel=Path(*module.split('.')).with_suffix('.lean')
    return (archive if module in meta['official_sources'] else root)/rel
for module,h in meta['sources'].items():
    assert sha(source(module))==h,module
    if module in meta['official_sources']:assert parent['sources'][module]==h
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',source(module).read_bytes(),re.M)
assert len(meta['sources'])==7 and len(meta['official_sources'])==6 and len(meta['local_sources'])==1
for name,h in meta['config_hashes'].items():assert sha(root/name)==h
if args.audit_only:
    print(json.dumps({'archive_hashes_passed':True,'local_source_modules':1,'parent_official_sources':6,'checker_from_parent':True,'lean_invoked':False}))
    raise SystemExit(0)
def executable(value):
    p=shutil.which(value);assert p is not None,'Executable not found: '+value
    return Path(p).resolve()
lean=executable(args.lean)
lake=executable(args.lake) if args.lake else lean.with_name('lake'+lean.suffix)
assert lake.is_file(),'Pass --lake pointing to the matching executable'
version=subprocess.check_output([str(lean),'--version'],text=True).strip()
assert 'version 4.35.0,' in version,version
label=args.run_name or datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
assert re.fullmatch(r'[A-Za-z0-9_-]+',label)
run=root/'runs'/label;project=run/'project';project.mkdir(parents=True,exist_ok=False)
evidence=run/'evidence';evidence.mkdir()
for module in meta['order']:
    rel=Path(*module.split('.')).with_suffix('.lean');p=project/rel;p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(source(module).read_bytes())
for n in ['lakefile.toml','lean-toolchain']:(project/n).write_bytes((root/n).read_bytes())
(project/'Check.lean').write_bytes((archive/'Check.lean').read_bytes())
assert not (project/'.lake').exists()
env=dict(os.environ);env.pop('LEAN_PATH',None)
env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','');env['LEAN_NUM_THREADS']='1'
def execute(cmd,log):
    start=time.monotonic()
    with log.open('wb') as f:p=subprocess.run(cmd,cwd=project,env=env,stdout=f,stderr=subprocess.STDOUT)
    if p.returncode:
        print(log.read_text(encoding='utf-8',errors='replace')[-12000:]);p.check_returncode()
    return time.monotonic()-start
seconds=execute([str(lake),'build',*meta['build_targets']],evidence/'lake-build.log')
checks=[]
for module,heads in meta['heads'].items():
    cmd=[str(lake),'env',str(lean),'--run','Check.lean',module,'--claim','partial']
    for h in heads:cmd+=['--headline',h]
    log=evidence/(module+'.check.log');elapsed=execute(cmd,log)
    c=json.loads(next(s for s in reversed(log.read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms']
    assert c['replay']['constants']==meta['expected_constants'][module]
    assert [h['name'] for h in c['headlines']]==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    checks.append({'module':module,'seconds':elapsed,'result':c})
types=''.join('import '+m+'\n' for m in meta['heads'])+''.join('#check @'+h+'\n#print axioms '+h+'\n' for hs in meta['heads'].values() for h in hs)
(project/'CheckNewTypes.lean').write_text(types,encoding='utf-8',newline='\n')
execute([str(lake),'env',str(lean),'CheckNewTypes.lean'],evidence/'Types.log')
normalize=lambda s:re.sub(r'\s+','',s)
assert normalize((evidence/'Types.log').read_text(encoding='utf-8'))==normalize((root/'evidence/fresh7/Types.log').read_text(encoding='utf-8'))
objects={}
for module,h in meta['sources'].items():
    rel=Path(*module.split('.')).with_suffix('.lean');assert sha(project/rel)==h
    objects[module]=sha(project/'.lake/build/lib/lean'/rel.with_suffix('.olean'))
assert sha(project/'Check.lean')==meta['checker_sha256']
result={'passed':True,'official_pin':meta['official_pin'],'fresh_sources':7,'reference_objects_used':False,'external_LEAN_PATH_cleared':True,'core_only':True,'build_seconds':seconds,'source_hashes':meta['sources'],'object_hashes':objects,'checks':checks,'constants':37,'headlines':6,'printed_types_and_axioms_match':True,'checker_sha256':meta['checker_sha256'],'lean_version':version,'lean_binary_sha256':sha(lean),'source_warning':b'warning:' in (evidence/'lake-build.log').read_bytes(),'historical_three_import_smoke_rerun':False}
(evidence/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':True,'fresh_sources':7,'constants':37,'headlines':6,'historical_smoke_rerun':False}))
