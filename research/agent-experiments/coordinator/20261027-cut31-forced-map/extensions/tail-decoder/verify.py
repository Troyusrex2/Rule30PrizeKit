"""Fresh 22-source reproduction from the immutable parent and this one-source extension."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,shutil,subprocess,time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--parent',type=Path,help='Parent archive root; default is two directories above this extension')
parser.add_argument('--lean',default='lean',help='Already installed Lean 4.35.0 executable')
parser.add_argument('--lake',default=None,help='Matching Lake executable; default is beside Lean')
parser.add_argument('--run-name')
parser.add_argument('--audit-only',action='store_true',help='Read/hash only; do not invoke Lean or Lake')
args=parser.parse_args()
ext=Path(__file__).resolve().parent
parent=args.parent.resolve() if args.parent else ext.parent.parent
read=lambda p:json.loads(p.read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
meta=read(ext/'EXTENSION.json')
assert sha(parent/'MANIFEST.json')==meta['parent_manifest_sha256'],'Wrong parent archive'
assert sha(parent/'SOURCES.json')==meta['parent_sources_metadata_sha256']
for root in [parent,ext]:
    for item in read(root/'MANIFEST.json')['files']:
        rel=Path(item['path'])
        assert not rel.is_absolute() and '..' not in rel.parts
        assert sha(root/rel)==item['sha256'] and (root/rel).stat().st_size==item['bytes'],rel
pm=read(parent/'SOURCES.json')
assert len(pm['sources'])==21 and pm['official_pin']==meta['official_pin']
assert sha(parent/'Check.lean')==meta['parent_checker_sha256']==pm['checker_sha256']
module=meta['module'];source=ext/(module+'.lean')
assert sha(source)==meta['source_sha256']
for m,digest in pm['sources'].items():
    assert sha(parent/Path(*m.split('.')).with_suffix('.lean'))==digest
for rel,digest in pm['config_hashes'].items():assert sha(parent/rel)==digest
assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',source.read_bytes(),re.M)
if args.audit_only:
    print(json.dumps({'hashes_passed':True,'parent_sources':21,'extension_sources':1,'lean_invoked':False}))
    raise SystemExit(0)

def executable(s):
    value=shutil.which(s)
    assert value,'Executable not found: '+s
    return Path(value).resolve()
lean=executable(args.lean)
lake=executable(args.lake) if args.lake else lean.with_name('lake'+lean.suffix)
assert lake.is_file(),'Supply the matching Lake executable'
version=subprocess.check_output([str(lean),'--version'],text=True).strip()
assert 'version 4.35.0,' in version,version
name=args.run_name or datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
assert re.fullmatch(r'[A-Za-z0-9_-]+',name)
run=ext/'runs'/name;project=run/'project';project.mkdir(parents=True,exist_ok=False)
evidence=run/'evidence';evidence.mkdir()
for m in pm['order']:
    rel=Path(*m.split('.')).with_suffix('.lean')
    target=project/rel;target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes((parent/rel).read_bytes())
(project/(module+'.lean')).write_bytes(source.read_bytes())
for rel in ['Check.lean','lean-toolchain']:(project/rel).write_bytes((parent/rel).read_bytes())
config=(parent/'lakefile.toml').read_bytes()+('\n[[lean_lib]]\nname = "'+module+'"\n').encode()
(project/'lakefile.toml').write_bytes(config)
assert not (project/'.lake').exists()
env=dict(os.environ);env.pop('LEAN_PATH',None)
env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
env['LEAN_NUM_THREADS']='1'
def execute(command,log):
    start=time.monotonic()
    with log.open('wb') as stream:
        done=subprocess.run(command,cwd=project,env=env,stdout=stream,stderr=subprocess.STDOUT)
    if done.returncode:
        print(log.read_text(encoding='utf-8',errors='replace')[-12000:]);done.check_returncode()
    return time.monotonic()-start
build_seconds=execute([str(lake),'build',module],evidence/'lake-build.log')
heads=dict(pm['heads']);heads[module]=meta['heads']
expected=dict(pm['expected_constants']);expected[module]=meta['constants']
checks=[]
for m,hs in heads.items():
    command=[str(lake),'env',str(lean),'--run','Check.lean',m,'--claim','partial']
    for h in hs:command+=['--headline',h]
    log=evidence/(m+'.check.log');seconds=execute(command,log)
    verdict=json.loads(next(s for s in reversed(log.read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
    assert verdict['verdict']=='pass' and verdict['replay']['ok'] and not verdict['newAxioms']
    assert verdict['replay']['constants']==expected[m]
    assert [h['name'] for h in verdict['headlines']]==hs
    assert all(h['ok'] and h['typeMatches'] for h in verdict['headlines'])
    checks.append({'module':m,'seconds':seconds,'checker':verdict})
types=''.join('import '+m+'\n' for m in heads)+''.join('#check @'+h+'\n#print axioms '+h+'\n' for hs in heads.values() for h in hs)
(project/'Types.lean').write_text(types,encoding='utf-8',newline='\n')
execute([str(lake),'env',str(lean),'Types.lean'],evidence/'Types.log')
expected_types=(parent/'evidence/root-full-lake/Types.log').read_text(encoding='utf-8')+(ext/'evidence/root/Types.log').read_text(encoding='utf-8')
normalize=lambda s:re.sub(r'\s+','',s)
assert normalize((evidence/'Types.log').read_text(encoding='utf-8'))==normalize(expected_types)
sources=dict(pm['sources']);sources[module]=meta['source_sha256']
objects={}
for m,digest in sources.items():
    rel=Path(*m.split('.')).with_suffix('.lean')
    assert sha(project/rel)==digest
    objects[m]=sha(project/'.lake/build/lib/lean'/rel.with_suffix('.olean'))
assert sha(project/'Check.lean')==meta['parent_checker_sha256']
assert (project/'lakefile.toml').read_bytes()==config
constants=sum(c['checker']['replay']['constants'] for c in checks)
assert constants==410 and sum(map(len,heads.values()))==12
result={'passed':True,'fresh_sources':22,'reference_objects_used':False,'external_LEAN_PATH_cleared':True,
 'core_only':True,'official_pin':meta['official_pin'],'parent_manifest_sha256':meta['parent_manifest_sha256'],
 'source_hashes':sources,'object_hashes':objects,'checks':checks,'constants':constants,'headlines':12,
 'printed_types_and_axioms_match':True,'source_warning':b'warning:' in (evidence/'lake-build.log').read_bytes(),
 'build_seconds':build_seconds,'checker_sha256':sha(project/'Check.lean'),'lean_version':version,'lean_binary_sha256':sha(lean)}
(evidence/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':True,'fresh_sources':22,'constants':410,'headlines':12}))
