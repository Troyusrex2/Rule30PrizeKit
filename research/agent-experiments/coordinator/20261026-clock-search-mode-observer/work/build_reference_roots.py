from pathlib import Path
import subprocess,os,time,json,hashlib
r=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload';p=r/'project'
lean=owner/'_cache/payload/toolchain/bin/lean.exe';lib=p/'.lake/build/lib/lean'
assert hashlib.sha256((p/'Check.lean').read_bytes()).hexdigest()=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
env=dict(os.environ,LEAN_PATH=str(lib),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
stages=[]
for module,source in [('Ruliology.CellularAutomata.Rule30WhitePadding','lean/Ruliology/CellularAutomata/Rule30WhitePadding.lean'),
                      ('Rule30Equivalents.P2Scales','equivalents/Rule30Equivalents/P2Scales.lean'),
                      ('Rule30Equivalents','equivalents/Rule30Equivalents.lean'),
                      ('Rule30PrizeKit','Rule30PrizeKit.lean')]:
    start=time.monotonic();target=lib/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
    logfile=r/'evidence'/('reference-'+module+'.log')
    with logfile.open('wb') as log:
        z=subprocess.run([str(lean),'-o',str(target),source],cwd=p,env=env,stdout=log,stderr=subprocess.STDOUT)
    stages.append({'module':module,'exit_code':z.returncode,'seconds':round(time.monotonic()-start,3)})
    if z.returncode:print(logfile.read_text(encoding='utf-8',errors='replace')[-5000:],flush=True)
    z.check_returncode()
(r/'reference-build-report.json').write_text(json.dumps({'passed':True,'stages':stages},indent=2)+'\n')
print(json.dumps({'passed':True,'stages':stages}),flush=True)
