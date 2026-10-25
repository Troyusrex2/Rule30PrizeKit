"""Owned fixed-ID logs; retain every guard outcome even if one case fails."""
import concurrent.futures,hashlib,json,os,sys
from pathlib import Path
root=Path(__file__).resolve().parent;sys.path.insert(0,str(Path.home()/'Rule30-offload/_cache/payload'))
from worker import guarded
assert (root/'OWNER.txt').read_text().strip()=='Rule30 explicit finite-history sparse ranks, robust harness v2; 2026-10-25'
for name,digest in json.loads((root/'sources.json').read_text()).items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
env=os.environ.copy();env.update({'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','PYTHONUTF8':'1','RULE30_GRAPH_CONTROLS_ONLY':'1'});cache=root/'_cache';cache.mkdir(exist_ok=True);limits={'seconds':300,'rss_gib':12,'minimum_free_gib':16}
control=guarded([sys.executable,'-X','utf8',str(root/'left_finite_history_controls.py')],root,env,cache/'controls.log',limits)
assert control['exit_code']==0 and not control['guard_stop'],control
cases=[(2,'vacuum',13,'1'),(2,'vacuum',13,'3/2'),(3,'vacuum',13,'1'),(3,'last3',13,'1'),(3,'last3',13,'2'),(4,'zero',13,'1')]
def run(i,case):
 depth,reader,H,scale=case;return {'case':case,**guarded([sys.executable,'-X','utf8',str(root/'left_finite_past_cases.py'),'--depth',str(depth),'--reader',reader,'--horizon',str(H),'--scale',scale],root,env,cache/('case-'+str(i)+'.log'),limits)}
records=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 futures={pool.submit(run,i,case):case for i,case in enumerate(cases)}
 for future in concurrent.futures.as_completed(futures):
  try:r=future.result()
  except Exception as e:r={'case':futures[future],'harness_exception':type(e).__name__+': '+str(e),'outcome':'unknown'}
  records.append(r);(root/'guard-report.json').write_text(json.dumps({'controls':control,'records':records},indent=2)+'\n',encoding='utf-8');print(r,flush=True)
sys.exit(0 if len(records)==len(cases) and all(r.get('exit_code')==0 and not r.get('guard_stop') and 'harness_exception' not in r for r in records) else 1)
