from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
root=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
module=sys.argv[1]
specs={'Rule30PeriodicOrPeriodResearch':['actual_periodic_or_double_period'],
'Rule30PeriodicOrPairCertificate':['base_check','successors_check','closed_check','excludes_check'],
'Rule30TwoPlateauClockResearch':['actual_even_two_plateau_or_clock_rigidity','actual_third_column_no_half_period','actual_third_column_no_eventual_half_period']}
assert module in specs
reference=owner/'research/verifier9-20261026/project'
checker=reference/'Check.lean';expected='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected
lean=owner/'_cache/payload/toolchain/bin/lean.exe';lib=root/'lib';lib.mkdir(exist_ok=True)
out=root/'formal'/module;out.mkdir(parents=True,exist_ok=True)
source=root/(module+'.lean');raw=source.read_bytes()
assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',raw,re.M)
env=dict(os.environ,LEAN_PATH=str(lib)+';'+str(owner/'research/physical-center-20261026T1512/lib')+';'+str(reference/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
start=time.monotonic()
with (out/'build.log').open('wb') as stream:
    build=subprocess.run([str(lean),'-o',str(lib/(module+'.olean')),str(source)],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
if build.returncode:
    print((out/'build.log').read_text(encoding='utf-8',errors='replace')[-4500:]);build.check_returncode()
compile_time=time.monotonic()-start
argv=[str(lean),'--run',str(checker),module,'--claim','partial']
for head in specs[module]:argv+=['--headline',module+'.'+head]
with (out/'check.log').open('wb') as stream:
    check=subprocess.run(argv,cwd=reference,env=env,stdout=stream,stderr=subprocess.STDOUT)
if check.returncode:
    print((out/'check.log').read_text(encoding='utf-8',errors='replace')[-4500:]);check.check_returncode()
report=json.loads(next(x for x in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
assert report['verdict']=='pass' and report['replay']['ok'] and not report['newAxioms'] and all(h['ok'] for h in report['headlines'])
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected
data={'passed':True,'module':module,'source_sha256':hashlib.sha256(raw).hexdigest(),
      'compiled_module_sha256':hashlib.sha256((lib/(module+'.olean')).read_bytes()).hexdigest(),
      'checker_sha256':expected,'pin':'5473ffd075f63c9d626e63b8455805d4831b39ca',
      'compile_seconds':compile_time,'total_seconds':time.monotonic()-start,'checker':report}
(out/'report.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print(f'{module}: full replay pass, {report["replay"]["constants"]} constants.')
