"""Fresh core-Lean reproduction. No SSH, external libraries or compiled contribution cache."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,subprocess,time

parser=argparse.ArgumentParser()
parser.add_argument('--lean',default='lean')
parser.add_argument('--run-name',default=None)
args=parser.parse_args()
root=Path(__file__).resolve().parent
meta=json.loads((root/'SOURCES.json').read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(root/'Check.lean')==meta['checker_sha256']
for name,digest in meta['sources'].items():
    src=root/Path(*name.split('.')).with_suffix('.lean')
    assert sha(src)==digest,name
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',src.read_bytes(),re.M),name
version=subprocess.check_output([args.lean,'--version'],text=True).strip()
assert 'version 4.35.0,' in version,version
run_name=args.run_name or datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
assert re.fullmatch(r'[A-Za-z0-9_-]+',run_name)
run=root/'runs'/run_name;run.mkdir(parents=True,exist_ok=False)
lib=run/'lib';lib.mkdir()
evidence=run/'evidence';evidence.mkdir()
env=dict(os.environ,LEAN_PATH=str(lib),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
def execute(command,log):
    begin=time.monotonic()
    with log.open('wb') as stream:
        result=subprocess.run(command,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
    seconds=time.monotonic()-begin
    if result.returncode:
        print(log.read_text(encoding='utf-8',errors='replace')[-12000:])
        result.check_returncode()
    return seconds
builds=[];checks=[];all_types=[]
for name in meta['official_order']+meta['modules']:
    rel=Path(*name.split('.'))
    obj=lib/rel.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
    log=evidence/(name+'.build.log')
    seconds=execute([args.lean,'-o',str(obj),rel.with_suffix('.lean').as_posix()],log)
    builds.append({'module':name,'source_sha256':meta['sources'][name],
                   'object_sha256':sha(obj),'seconds':seconds,'build_log_sha256':sha(log),
                   'freshly_built':True,'warnings_in_source_build':b'warning:' in log.read_bytes()})
    if name in meta['modules']:
        log=evidence/(name+'.check.log')
        cmd=[args.lean,'--run','Check.lean',name,'--claim','partial']
        for head in meta['heads'][name]:cmd+=['--headline',head]
        check_seconds=execute(cmd,log)
        verdict=json.loads(next(s for s in reversed(log.read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
        assert verdict['verdict']=='pass' and verdict['replay']['ok'] and not verdict['newAxioms']
        assert verdict['replay']['constants']==meta['expected_constants'][name]
        assert all(h['ok'] for h in verdict['headlines'])
        types=evidence/(name+'.types.lean')
        types.write_text('import '+name+'\n'+''.join('#check '+h+'\n#print axioms '+h+'\n' for h in meta['heads'][name]),encoding='utf-8',newline='\n')
        types_log=evidence/(name+'.types.log')
        type_seconds=execute([args.lean,types.relative_to(root).as_posix()],types_log)
        all_types.append(types_log.read_text(encoding='utf-8'))
        checks.append({'module':name,'source_sha256':meta['sources'][name],
                       'constants':verdict['replay']['constants'],'headlines':len(verdict['headlines']),
                       'check_seconds':check_seconds,'type_seconds':type_seconds,
                       'checker_result':verdict,'check_log_sha256':sha(log),'types_sha256':sha(types_log)})
        print(json.dumps({'module':name,'constants':checks[-1]['constants'],'headlines':checks[-1]['headlines']}),flush=True)
assert re.sub(r'\s+','', ''.join(all_types))==re.sub(r'\s+','',(root/'evidence/canonical-lake/Types.log').read_text(encoding='utf-8'))
assert sha(root/'Check.lean')==meta['checker_sha256']
result={'passed':True,'official_pin':meta['official_pin'],'core_only':True,'mathlib_used':False,
        'external_LEAN_PATH_cleared':True,'fresh_source_count':len(builds),'builds':builds,'checks':checks,
        'constants':sum(c['constants'] for c in checks),'headlines':sum(c['headlines'] for c in checks),
        'lean_version':version,'checker_sha256':meta['checker_sha256']}
(evidence/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'passed':True,'fresh_sources':len(builds),'constants':result['constants'],'headlines':result['headlines']}))
