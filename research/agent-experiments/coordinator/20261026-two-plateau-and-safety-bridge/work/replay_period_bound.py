from pathlib import Path
import hashlib,json,os,subprocess,time
root=Path(__file__).resolve().parent
owner=Path.home()/'Rule30-offload'
assert root.is_relative_to(owner)
reference=owner/'research/verifier9-20261026/project'
checker=reference/'Check.lean'
checkhash='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==checkhash
lean=owner/'_cache/payload/toolchain/bin/lean.exe'
library=root/'lib';library.mkdir(exist_ok=True)
env=dict(os.environ,LEAN_PATH=str(library)+';'+str(reference/'.lake/build/lib/lean'),
    LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
module='Rule30SaturatedOrPeriodResearch';source=root/(module+'.lean')
out=root/'formal';out.mkdir(exist_ok=True)
start=time.monotonic()
with (out/'build.log').open('wb') as stream:
    compiled=subprocess.run([str(lean),'-o',str(library/(module+'.olean')),str(source)],
        cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
if compiled.returncode:
    print((out/'build.log').read_text(encoding='utf-8',errors='replace')[-5000:]);compiled.check_returncode()
heads=[module+'.actual_saturated_or_double_period']
argv=[str(lean),'--run',str(checker),module,'--claim','partial']
for head in heads:argv+=['--headline',head]
with (out/'check.log').open('wb') as stream:
    checked=subprocess.run(argv,cwd=reference,env=env,stdout=stream,stderr=subprocess.STDOUT)
if checked.returncode:
    print((out/'check.log').read_text(encoding='utf-8',errors='replace')[-4000:]);checked.check_returncode()
report=json.loads(next(s for s in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if s.startswith('{')))
assert report['verdict']=='pass' and report['replay']['ok'] and not report['newAxioms']
assert all(h['ok'] for h in report['headlines'])
assert hashlib.sha256(checker.read_bytes()).hexdigest()==checkhash
summary={'passed':True,'module':module,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'checker_sha256':checkhash,'pin':'5473ffd075f63c9d626e63b8455805d4831b39ca',
    'seconds':time.monotonic()-start,'checker':report,'scope':'period bound only; plateau exclusion not yet proved'}
(out/'report.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print('Period-bound module compiled and fully kernel replayed.')
