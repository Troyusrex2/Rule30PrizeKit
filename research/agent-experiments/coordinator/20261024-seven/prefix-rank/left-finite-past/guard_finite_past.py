"""Two concurrent finite-past cases, with whole process-tree guards."""
import concurrent.futures,hashlib,json,os,sys
from pathlib import Path
root=Path(__file__).resolve().parent;sys.path.insert(0,str(Path.home()/'Rule30-offload/_cache/payload'))
from worker import guarded
assert (root/'OWNER.txt').read_text().strip()=='Rule30 exact finite-past sparse defect ranks; 2026-10-25'
for name,digest in json.loads((root/'sources.json').read_text()).items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
env=os.environ.copy();env.update({'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','PYTHONUTF8':'1'});cache=root/'_cache';cache.mkdir(exist_ok=True);limits={'seconds':300,'rss_gib':12,'minimum_free_gib':16}
control=guarded([sys.executable,'-X','utf8',str(root/'left_finite_past_controls.py')],root,env,cache/'controls.log',limits);assert control['exit_code']==0 and not control['guard_stop'],control
def run(case):
 reader,H,scale=case;r=guarded([sys.executable,'-X','utf8',str(root/'left_finite_past_cases.py'),'--reader',reader,'--horizon',str(H),'--scale',scale],root,env,cache/('-'.join(map(str,case))+'.log'),limits);return {'case':case,**r}
records=[];cases=[('zero',4,'1'),('last3',4,'1'),('vacuum',4,'1'),('vacuum',13,'1'),('vacuum',13,'2'),('last3',13,'2')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for future in concurrent.futures.as_completed([pool.submit(run,case) for case in cases]):
  r=future.result();records.append(r);(root/'guard-report.json').write_text(json.dumps({'controls':control,'records':records},indent=2)+'\n',encoding='utf-8');print(r,flush=True)
sys.exit(0 if len(records)==len(cases) and all(r['exit_code']==0 and not r['guard_stop'] for r in records) else 1)
