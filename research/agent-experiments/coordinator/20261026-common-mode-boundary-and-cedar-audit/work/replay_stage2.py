from pathlib import Path
import hashlib,json,os,re,subprocess,time
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
reference=owner/'research/verifier9-20261026/project'
lean=owner/'_cache/payload/toolchain/bin/lean.exe'
checker=reference/'Check.lean';checker_hash='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==checker_hash
meta=json.loads((root/'source-manifest.json').read_bytes());assert meta['official_pin']=='5473ffd075f63c9d626e63b8455805d4831b39ca'
lib=root/'lib';lib.mkdir(exist_ok=True);out=root/'root-formal';out.mkdir(exist_ok=True)
env=dict(os.environ,LEAN_PATH=str(lib)+';'+str(reference/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
start=time.monotonic();results=[];builds=[]
for item in meta['dependencies']+meta['modules']:
    module=item['module'];source=root/(module+'.lean');raw=source.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==item['source_sha256']
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',raw,re.M)
    t=time.monotonic()
    with (out/('build-'+module+'.log')).open('wb') as stream:
        z=subprocess.run([str(lean),'-o',str(lib/(module+'.olean')),str(source)],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
    z.check_returncode();builds.append({'module':module,'seconds':time.monotonic()-t,'source_sha256':item['source_sha256']})
    if item not in meta['modules']:continue
    argv=[str(lean),'--run',str(checker),module,'--claim','partial']
    for head in item['headlines']:
        assert head.startswith(module+'.');argv+=['--headline',head]
    with (out/('check-'+module+'.log')).open('wb') as stream:
        z=subprocess.run(argv,cwd=reference,env=env,stdout=stream,stderr=subprocess.STDOUT)
    z.check_returncode()
    report=json.loads(next(line for line in reversed((out/('check-'+module+'.log')).read_text(encoding='utf-8').splitlines()) if line.startswith('{')))
    assert report['verdict']=='pass' and report['replay']['ok'] and not report['newAxioms']
    assert all(h['ok'] and h['typeMatches'] for h in report['headlines'])
    result={'module':module,'source_sha256':item['source_sha256'],'seconds':time.monotonic()-t,'checker':report}
    (out/(module+'-report.json')).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    results.append(result);print(module+': full replay PASS '+str(report['replay']['constants'])+' constants.',flush=True)
assert hashlib.sha256(checker.read_bytes()).hexdigest()==checker_hash
(out/'report.json').write_text(json.dumps({'passed':True,'pin':meta['official_pin'],'checker_sha256':checker_hash,
    'seconds':time.monotonic()-start,'dependency_builds':builds,'new_modules':results,
    'scope':'Two Cedar partial results; no safety completeness or physical-center claim'},indent=2)+'\n',encoding='utf-8')
