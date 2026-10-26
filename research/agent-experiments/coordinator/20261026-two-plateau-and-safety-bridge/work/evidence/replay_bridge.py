from pathlib import Path
import hashlib,json,os,re,subprocess,time
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
ref=owner/'research/verifier9-20261026/project';lib=root/'lib';lib.mkdir(exist_ok=True)
check=ref/'Check.lean';checkhash='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(check.read_bytes()).hexdigest()==checkhash
lean=owner/'_cache/payload/toolchain/bin/lean.exe'
env=dict(os.environ,LEAN_PATH=str(lib)+';'+str(ref/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
meta=json.loads((root/'source-manifest.json').read_bytes());assert meta['official_pin']=='5473ffd075f63c9d626e63b8455805d4831b39ca'
base=root/'CedarSafetySoundness.lean'
assert hashlib.sha256(base.read_bytes()).hexdigest()=='e2e17bdb5be676ba8739a477e88e7e0ffc00da58422eb88c4b37303c26165e1a'
out=root/'root-formal';out.mkdir(exist_ok=True);start=time.monotonic();results=[]
with (out/'build-CedarSafetySoundness.log').open('wb') as stream:
    z=subprocess.run([str(lean),'-o',str(lib/'CedarSafetySoundness.olean'),str(base)],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
z.check_returncode()
for m in meta['modules']:
    module=m['module'];assert module in ['CedarSafetySemantics','CedarSafetyBridge','CedarWhiteTransport']
    source=root/(module+'.lean');raw=source.read_bytes();assert hashlib.sha256(raw).hexdigest()==m['source_sha256']
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',raw,re.M)
    t=time.monotonic()
    with (out/('build-'+module+'.log')).open('wb') as stream:
        z=subprocess.run([str(lean),'-o',str(lib/(module+'.olean')),str(source)],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
    z.check_returncode()
    argv=[str(lean),'--run',str(check),module,'--claim','partial']
    for head in m['headlines']:
        assert head.startswith(('CedarSafety.','CedarSafetyBridge.','CedarWhiteTransport.'))
        argv+=['--headline',head]
    with (out/('check-'+module+'.log')).open('wb') as stream:
        z=subprocess.run(argv,cwd=ref,env=env,stdout=stream,stderr=subprocess.STDOUT)
    z.check_returncode()
    report=json.loads(next(s for s in reversed((out/('check-'+module+'.log')).read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
    assert report['verdict']=='pass' and report['replay']['ok'] and not report['newAxioms'] and all(h['ok'] for h in report['headlines'])
    result={'module':module,'source_sha256':m['source_sha256'],'seconds':time.monotonic()-t,'checker':report}
    results.append(result);(out/(module+'-report.json')).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(module+': '+str(report['replay']['constants'])+' constants fully replayed.',flush=True)
assert hashlib.sha256(check.read_bytes()).hexdigest()==checkhash
(out/'report.json').write_text(json.dumps({'passed':True,'pin':meta['official_pin'],'checker_sha256':checkhash,
    'seconds':time.monotonic()-start,'new_modules':results,
    'dependency_note':'Exact F002 source separately fully replayed by root in cedar-review-20261026T1539; rebuilt here with matching SHA.'},indent=2)+'\n',encoding='utf-8')
