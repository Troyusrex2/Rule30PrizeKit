from pathlib import Path
import hashlib,json,os,re,subprocess,time,shutil,sys
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
module=sys.argv[1]
heads={'HeightOneLogic':['span_one_of_closed_period','isolated_derivative','isolated_forces_twins'],
       'HeightOneSemantics':['leaf_flip_trace','leaf_flip_return','return8_twins_two'],
       'HeightOneTransfer':['height_one_shorter_counterexample'],
       'HeightOnePeriodicity':['exists_even_column_period','alltime_height_one_shorter_counterexample','least_column_above_four_transfer'],
       'HeightOneDescent':['height_one_nonreturn_shorter','height_one_return_of_shorter_completeness','minimal_safe_counterexample_not_height_one']}
assert module in heads
ref=owner/'research/verifier9-20261026/project';checker=ref/'Check.lean'
ch='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==ch
meta=json.loads((root/'sources.json').read_text());phases=[]
for name,d in meta['dependencies'].items():
 p=owner/'research'/d['phase']
 assert hashlib.sha256((p/(name+'.lean')).read_bytes()).hexdigest()==d['source_sha256']
 assert hashlib.sha256((p/'lib'/(name+'.olean')).read_bytes()).hexdigest()==d['compiled_sha256']
 if str(p/'lib') not in phases:phases.append(str(p/'lib'))
lean=owner/'_cache/payload/toolchain/bin/lean.exe';lib=root/'lib';lib.mkdir(exist_ok=True)
env=dict(os.environ,LEAN_PATH=';'.join([str(lib),*phases,str(ref/'.lake/build/lib/lean')]),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
out=root/'formal'/module;out.mkdir(parents=True,exist_ok=True)
if (out/'build.log').exists():shutil.copytree(out,root/'attempts'/str(time.time_ns())/module)
source=root/(module+'.lean');raw=source.read_bytes();assert hashlib.sha256(raw).hexdigest()==meta['sources'][module]
assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',raw,re.M)
shutil.copyfile(source,out/'source.lean')
start=time.monotonic()
def run(args,path,cwd):
 with path.open('wb') as stream:r=subprocess.run(args,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
 if r.returncode:print(path.read_text(encoding='utf-8',errors='replace')[-6000:]);r.check_returncode()
run([str(lean),'-o',str(lib/(module+'.olean')),str(source)],out/'build.log',root)
build=time.monotonic()-start
args=[str(lean),'--run',str(checker),module,'--claim','partial']
for head in heads[module]:args+=['--headline',module+'.'+head]
run(args,out/'check.log',ref)
c=json.loads(next(x for x in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] for h in c['headlines'])
report={'passed':True,'source_sha256':hashlib.sha256(raw).hexdigest(),'compiled_sha256':hashlib.sha256((lib/(module+'.olean')).read_bytes()).hexdigest(),'pin':'5473ffd075f63c9d626e63b8455805d4831b39ca','checker_sha256':ch,'build_seconds':build,'total_seconds':time.monotonic()-start,'checker':c}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
assert hashlib.sha256(checker.read_bytes()).hexdigest()==ch
print(json.dumps({'module':module,'passed':True,'constants':c['replay']['constants']}))
