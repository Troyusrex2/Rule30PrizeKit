from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
module=sys.argv[1]
heads={'RootAntiPeriodHeight':['paired_height_identity','safe_complement_height_difference','height_three_periods','safe_complement_zero_drift','anti_period_safe_necessary','not_safe_of_height_obstruction'],'RootEventHeight':['signed_height_identity','even_return_signed_sums','even_period_signed_sums','marked_correction_range','event_iff_zero_pair','safe_marked_height_range','safe_height_white_initial','safe_height_black_initial'],'CedarD3Converse':['accepted_near_prefix','accepted_normalized_safe_prefix','d3_of_return_complete','d3_iff_return_complete']}
assert module in heads
ref=owner/'research/verifier9-20261026/project';checker=ref/'Check.lean';ch='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==ch
metadata=json.loads((root/'sources.json').read_bytes());prior=owner/'research'/metadata['prior_dependency_phase']
for name,item in metadata['previous_own_root_dependencies'].items():
    assert hashlib.sha256((prior/(name+'.lean')).read_bytes()).hexdigest()==item['source_sha256']
    assert hashlib.sha256((prior/'lib'/(name+'.olean')).read_bytes()).hexdigest()==item['compiled_sha256']
if module=='RootAntiPeriodHeight':
    base=json.loads((root/'formal/RootEventHeight/report.json').read_bytes())
    assert hashlib.sha256((root/'lib/RootEventHeight.olean').read_bytes()).hexdigest()==base['compiled_sha256']
    assert base['source_sha256']==metadata['sources']['RootEventHeight']['sha256']
lean=owner/'_cache/payload/toolchain/bin/lean.exe';lib=root/'lib';lib.mkdir(exist_ok=True)
out=root/'formal'/module;out.mkdir(parents=True,exist_ok=True)
source=root/(module+'.lean');raw=source.read_bytes();assert hashlib.sha256(raw).hexdigest()==metadata['sources'][module]['sha256']
assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',raw,re.M)
env=dict(os.environ,LEAN_PATH=str(lib)+';'+str(prior/'lib')+';'+str(ref/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
start=time.monotonic()
def run(argv,path,cwd):
    with path.open('wb') as stream:r=subprocess.run(argv,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
    if r.returncode:
        print(path.read_text(encoding='utf-8',errors='replace')[-3000:]);r.check_returncode()
run([str(lean),'-o',str(lib/(module+'.olean')),str(source)],out/'build.log',root)
compile_seconds=time.monotonic()-start
argv=[str(lean),'--run',str(checker),module,'--claim','partial']
for name in heads[module]:argv+=['--headline',module+'.'+name]
run(argv,out/'check.log',ref)
c=json.loads(next(x for x in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] for h in c['headlines'])
assert hashlib.sha256(checker.read_bytes()).hexdigest()==ch
r={'passed':True,'module':module,'source_sha256':hashlib.sha256(raw).hexdigest(),'compiled_sha256':hashlib.sha256((lib/(module+'.olean')).read_bytes()).hexdigest(),'checker_sha256':ch,'pin':'5473ffd075f63c9d626e63b8455805d4831b39ca','compile_seconds':compile_seconds,'total_seconds':time.monotonic()-start,'checker':c}
(out/'report.json').write_bytes((json.dumps(r,indent=2)+'\n').encode())
print(json.dumps({'module':module,'passed':True,'constants':c['replay']['constants']}))
