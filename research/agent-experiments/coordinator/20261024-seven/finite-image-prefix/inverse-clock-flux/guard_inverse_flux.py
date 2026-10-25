"""Two concurrent guarded inverse-column flux searches, fixed log IDs."""
import concurrent.futures,hashlib,json,os,sys
from pathlib import Path
root=Path(__file__).resolve().parent;sys.path.insert(0,str(Path.home()/'Rule30-offload/_cache/payload'))
from worker import guarded
assert (root/'OWNER.txt').read_text().strip()=='Rule30 universal inverse-column signed geometric flux; 2026-10-25'
for name,digest in json.loads((root/'sources.json').read_text()).items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
env=os.environ.copy();env.update({'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','PYTHONUTF8':'1'});cache=root/'_cache';cache.mkdir(exist_ok=True);limits={'seconds':300,'rss_gib':12,'minimum_free_gib':16}
control=guarded([sys.executable,'-X','utf8',str(root/'inverse_clock_flux_controls.py')],root,env,cache/'controls.log',limits);assert control['exit_code']==0 and not control['guard_stop'],control
# columns,memory,boundary domain,spatial factor,spatial multiplier,clock
cases=[(2,4,'no00',1,1,1),(2,6,'no00',4,2,2),(2,6,'badclass',4,2,2),(3,4,'golden',4,1,1),(3,5,'golden',4,2,2),(3,6,'badclass',4,2,2),(3,6,'badclass',8,4,2),(2,6,'all',4,2,2)]
def run(i,case):
 c,k,domain,F,M,clock=case;cmd=[sys.executable,'-X','utf8',str(root/'inverse_flux_cases.py'),'--columns',str(c),'--memory',str(k),'--domain',domain,'--factor',str(F),'--multiplier',str(M),'--clock',str(clock)]
 return {'case':case,**guarded(cmd,root,env,cache/('case-'+str(i)+'.log'),limits)}
records=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 futures={pool.submit(run,i,case):case for i,case in enumerate(cases)}
 for future in concurrent.futures.as_completed(futures):
  try:r=future.result()
  except Exception as e:r={'case':futures[future],'harness_exception':type(e).__name__+': '+str(e),'outcome':'unknown'}
  records.append(r);(root/'guard-report.json').write_text(json.dumps({'controls':control,'records':records},indent=2)+'\n',encoding='utf-8');print(r,flush=True)
sys.exit(0 if len(records)==len(cases) and all(r.get('exit_code')==0 and not r.get('guard_stop') and 'harness_exception' not in r for r in records) else 1)
