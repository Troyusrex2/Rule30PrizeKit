from pathlib import Path
import hashlib,json,os,re,subprocess,time,shutil
root=Path(__file__).resolve().parent
owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
ref=owner/'research/verifier9-20261026/project'
checker=ref/'Check.lean'
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
ch='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==ch
lean=owner/'_cache/payload/toolchain/bin/lean.exe'
lib=root/'lib';lib.mkdir(exist_ok=True)
env=dict(os.environ,LEAN_PATH=str(lib)+';'+str(ref/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
modules={'Rule30CommonPastResearch':['actual_periodic'],
         'Rule30ColumnReaderResearch':['reader_sound'],
         'CedarSafetySoundness':['accepted_return_eight'],
         'CedarSafetySemantics':['trace_white'],
         'CedarSafetyBridge':['safe_return_iff_accepted'],
         'PrizeSafetyBridge':['safe_language_equal_reader','safe_equal_reader','safe_sink_separates']}
prefix={'CedarSafetySemantics':'CedarSafety'}
metadata=json.loads((root/'sources.json').read_text())
for module,heads in modules.items():
    out=root/'formal'/module;out.mkdir(parents=True,exist_ok=True)
    source=root/(module+'.lean');raw=source.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==metadata[module]['sha256']
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',raw,re.M)
    if (out/'report.json').exists():
        old=json.loads((out/'report.json').read_text())
        if old['source_sha256']==hashlib.sha256(raw).hexdigest() and old['compiled_sha256']==hashlib.sha256((lib/(module+'.olean')).read_bytes()).hexdigest():
            print(json.dumps({'module':module,'reused_own_fresh_replay':True}),flush=True)
            continue
    if (out/'build.log').exists():
        archive=root/'attempts'/str(time.time_ns())/module
        shutil.copytree(out,archive)
    start=time.monotonic()
    def run(args,path,cwd):
        with path.open('wb') as stream:r=subprocess.run(args,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
        if r.returncode:
            print(path.read_text(encoding='utf-8',errors='replace')[-5000:]);r.check_returncode()
    run([str(lean),'-o',str(lib/(module+'.olean')),str(source)],out/'build.log',root)
    build=time.monotonic()-start
    args=[str(lean),'--run',str(checker),module,'--claim','partial']
    for head in heads:args+=['--headline',prefix.get(module,module)+'.'+head]
    run(args,out/'check.log',ref)
    c=json.loads(next(x for x in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] for h in c['headlines'])
    report={'passed':True,'source_sha256':hashlib.sha256(raw).hexdigest(),'compiled_sha256':hashlib.sha256((lib/(module+'.olean')).read_bytes()).hexdigest(),'pin':pin,'checker_sha256':ch,'build_seconds':build,'total_seconds':time.monotonic()-start,'checker':c}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'module':module,'passed':True,'constants':c['replay']['constants']}),flush=True)
assert hashlib.sha256(checker.read_bytes()).hexdigest()==ch
