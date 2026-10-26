from pathlib import Path
import subprocess,os,json,time
r=Path(__file__).resolve().parent;owner=Path.home()/'Rule30-offload';p=r/'project'
env=dict(os.environ,LEAN_PATH=str(p/'.lake/build/lib/lean'),LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
out=r/'reference-formal/Rule30Equivalents.P2Scales';out.mkdir(parents=True,exist_ok=True)
heads=['Rule30Equivalents.P2Scales.problem2_iff_singleSequence','Rule30Equivalents.P2Scales.problem2_iff_firstPassage']
args=[str(owner/'_cache/payload/toolchain/bin/lean.exe'),'--run',str(p/'Check.lean'),
      'Rule30Equivalents.P2Scales','--claim','partial']+sum((['--headline',h] for h in heads),[])
start=time.monotonic()
with (out/'check.log').open('wb') as f:z=subprocess.run(args,cwd=p,env=env,stdout=f,stderr=subprocess.STDOUT)
if z.returncode:print((out/'check.log').read_text(encoding='utf-8')[-6000:])
z.check_returncode()
c=json.loads(next(x for x in reversed((out/'check.log').read_text(encoding='utf-8').splitlines()) if x.startswith('{')))
assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms']
(out/'report.json').write_text(json.dumps({'passed':True,'check':c,'seconds':time.monotonic()-start,
 'kit_commit':'5473ffd075f63c9d626e63b8455805d4831b39ca','used_to_claim_P1_progress':False},indent=2)+'\n')
print(json.dumps({'passed':True,'replay':c['replay'],'used_to_claim_P1_progress':False}))
