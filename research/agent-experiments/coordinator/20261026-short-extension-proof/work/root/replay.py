from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
module=sys.argv[1]
heads={'CedarWhiteTransport':['safe_white_padding','return8_white_padding'],'RootD3Reduction':['return_complete_of_d3','language_complete_of_d3','not_d3_of_not_return_complete'],'CedarSafetySoundness':['accepted_return_eight'],'CedarSafetySemantics':['safe_iff_window_of_return8'],'CedarSafetyBridge':['safe_return_iff_accepted'],'RootShortExtensionCore':['history_lift8','driven_cons','safe_cons'],'RootShortExtensionCases':['case_1_0','case_27_14'],'RootShortExtensionCertificate':['extension_certificate'],'RootShortExtension':['safe_short_extension','accepted_short_extension_language']}
names={'CedarSafetySemantics':'CedarSafety','RootShortExtensionCases':'RootShortExtensionCertificate'}
assert module in heads
ref=owner/'research/verifier9-20261026/project';checker=ref/'Check.lean'
checker_hash='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==checker_hash
lean=owner/'_cache/payload/toolchain/bin/lean.exe';lib=root/'lib';lib.mkdir(exist_ok=True)
out=root/'formal'/module;out.mkdir(parents=True,exist_ok=True)
src=root/(module+'.lean');raw=src.read_bytes()
assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',raw,re.M)
env=dict(os.environ,LEAN_PATH=str(lib)+';'+str(ref/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
start=time.monotonic()
def run(argv,path,cwd):
    with path.open('wb') as stream:r=subprocess.run(argv,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
    if r.returncode:
        print(path.read_text(encoding='utf-8',errors='replace')[-6000:]);r.check_returncode()
run([str(lean),'-o',str(lib/(module+'.olean')),str(src)],out/'build.log',root)
compile_seconds=time.monotonic()-start
argv=[str(lean),'--run',str(checker),module,'--claim','partial']
for head in heads[module]:argv+=['--headline',names.get(module,module)+'.'+head]
run(argv,out/'check.log',ref)
report=json.loads(next(x for x in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
assert report['verdict']=='pass' and report['replay']['ok'] and not report['newAxioms'] and all(h['ok'] for h in report['headlines'])
assert hashlib.sha256(checker.read_bytes()).hexdigest()==checker_hash
result={'passed':True,'module':module,'source_sha256':hashlib.sha256(raw).hexdigest(),'compiled_sha256':hashlib.sha256((lib/(module+'.olean')).read_bytes()).hexdigest(),'checker_sha256':checker_hash,'pin':'5473ffd075f63c9d626e63b8455805d4831b39ca','compile_seconds':compile_seconds,'total_seconds':time.monotonic()-start,'checker':report}
(out/'report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'module':module,'passed':True,'constants':report['replay']['constants'],'elapsed':result['total_seconds']}))
