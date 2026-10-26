from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload';assert root.is_relative_to(owner)
ref=owner/'research/verifier9-20261026/project';lean=owner/'_cache/payload/toolchain/bin/lean.exe'
checker=ref/'Check.lean';expected='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected
lib=root/'lib';lib.mkdir(exist_ok=True)
env=dict(os.environ,LEAN_PATH=str(lib)+';'+str(ref/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
heads={'CedarSafetySoundness':['accepted_return_eight'],'CedarSafetySemantics':['trace_white'],'CedarSafetyBridge':['safe_return_iff_accepted'],'CedarWhiteTransport':['take_evolution'],'RootShortExtensionCore':['driven_white'],'CedarNo11011':['finite_white_no11011'],'RootEventHeight':['signed_height_identity'],'HeightOneLogic':['span_one_of_closed_period'],'HeightOneSemantics':['leaf_flip_trace','leaf_flip_return'],'HeightTwoNearReturn':['certificate','whiteHeight_eq','height_two_short_extension','no_near_return_prefix'],'HeightTwoDescent':['coSafe_parent_descent','minimal_counterexample_parents']}
heads['HeightTwoPureMode']=['tiled_span_two','actual_parent_descent','minimal_height_two_not_tiled']
heads['HeightTwoMixedControl']=['all_time_local_constraints','newest_span_two','newest_not_eight','neither_parent_safe_or_coSafe','neither_parent_height_two']
def replay(module,attempt):
    source=root/(module+'.lean');raw=source.read_bytes()
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide|skipKernelTC)\b|^\s*axiom\b',raw,re.M)
    deps=json.loads((root/'dependencies.json').read_bytes())
    if module in deps:assert hashlib.sha256(raw).hexdigest()==deps[module]['sha256']
    out=root/'formal'/module/attempt;out.mkdir(parents=True,exist_ok=False);(out/'source.lean').write_bytes(raw)
    start=time.monotonic()
    def run(argv,log,cwd):
        with log.open('wb') as stream:proc=subprocess.run(argv,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
        if proc.returncode:
            print(log.read_text(encoding='utf-8',errors='replace')[-(1800 if log.name=='check.log' else 7000):]);raise SystemExit(proc.returncode)
    run([str(lean),'-o',str(lib/(module+'.olean')),str(source)],out/'build.log',root)
    compile_seconds=time.monotonic()-start
    argv=[str(lean),'--run',str(checker),module,'--claim','partial']
    namespace='CedarSafety' if module=='CedarSafetySemantics' else module
    for head in heads[module]:argv+=['--headline',namespace+'.'+head]
    run(argv,out/'check.log',ref)
    report=json.loads(next(x for x in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
    assert report['verdict']=='pass' and report['replay']['ok'] and not report['newAxioms'] and all(h['ok'] for h in report['headlines'])
    data={'passed':True,'module':module,'attempt':attempt,'source_sha256':hashlib.sha256(raw).hexdigest(),'compiled_sha256':hashlib.sha256((lib/(module+'.olean')).read_bytes()).hexdigest(),'checker_sha256':expected,'compile_seconds':compile_seconds,'total_seconds':time.monotonic()-start,'checker':report}
    (out/'report.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'passed':True,'module':module,'declarations':report['replay']['constants'],'seconds':data['total_seconds']}),flush=True)
if sys.argv[1].startswith('dependencies'):
    for module in ['CedarSafetySoundness','CedarSafetySemantics','CedarSafetyBridge','CedarWhiteTransport','RootShortExtensionCore','CedarNo11011','RootEventHeight','HeightOneLogic','HeightOneSemantics','HeightTwoNearReturn','HeightTwoDescent']:
        passed=list((root/'formal'/module).glob('*/report.json')) if (root/'formal'/module).exists() else []
        if passed:
            assert json.loads(passed[-1].read_bytes())['source_sha256']==hashlib.sha256((root/(module+'.lean')).read_bytes()).hexdigest()
            print(module+': retaining this phase\'s successful fresh replay.',flush=True)
        else:replay(module,sys.argv[1])
else:replay(sys.argv[1],sys.argv[2])
