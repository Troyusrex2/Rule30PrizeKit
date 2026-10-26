from pathlib import Path
import hashlib,json,os,subprocess,time
ROOT=Path(__file__).resolve().parent
OWNER=Path.home()/'Rule30-offload'
assert OWNER.resolve() in ROOT.resolve().parents
project=OWNER/'research/notebook-offload-20261026/notebook/project'
lean=OWNER/'_cache/payload/toolchain/bin/lean.exe'
checker=project/'Check.lean'
expected_checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected_checker
module='Rule30SensorClosureResearch'
src=ROOT/(module+'.lean')
target=project/src.name
target.write_bytes(src.read_bytes())
env=dict(os.environ,LEAN_PATH=str(project/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
heads=[module+'.'+name for name in ['preimage_right_edge','field_nonlift','finite_sensor_nonlift']]
commands=[('build',[str(lean),'-o',str(project/'.lake/build/lib/lean'/(module+'.olean')),target.name]),
          ('check',[str(lean),'--run',str(checker),module,'--claim','partial']+
           sum((['--headline',h] for h in heads),[]))]
records=[]
for stage,argv in commands:
 start=time.monotonic();r=subprocess.run(argv,cwd=project,env=env,capture_output=True)
 (ROOT/(stage+'-sensor.log')).write_bytes(r.stdout+r.stderr)
 records.append({'stage':stage,'seconds':round(time.monotonic()-start,3),'exit_code':r.returncode})
 if r.returncode:print((r.stdout+r.stderr).decode('utf-8',errors='replace'),flush=True)
 r.check_returncode()
checked=json.loads(next(line for line in reversed(r.stdout.decode('utf-8').splitlines()) if line.startswith('{')))
assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
assert all(h['ok'] for h in checked['headlines'])
assert hashlib.sha256(checker.read_bytes()).hexdigest()==expected_checker
report={'passed':True,'machine':'G913','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
        'kit_commit':'0090056412733accaa27643d3cbbf982104f2251','checker_sha256':expected_checker,
        'checker_unchanged':True,'stages':records,'check':checked,'full_problem_solved':False,
        'all_time_observer_counterexample':False}
(ROOT/'sensor-kernel-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'replay':checked['replay'],'headlines':len(heads),'source_sha256':report['source_sha256']}),flush=True)
