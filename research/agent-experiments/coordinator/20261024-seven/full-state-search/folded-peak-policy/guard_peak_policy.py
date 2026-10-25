"""Run four independent owned prefix-peak strategy shards on G913."""
import concurrent.futures,hashlib,json,os,sys
from pathlib import Path
root=Path(__file__).resolve().parent;sys.path.insert(0,str(Path.home()/'Rule30-offload/_cache/payload'))
from worker import guarded
assert (root/'OWNER.txt').read_text().strip()=='Rule30 full-row prefix-peak policy search; 2026-10-25'
for n,h in json.loads((root/'sources.json').read_text()).items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h,n
cache=root/'_cache';cache.mkdir(exist_ok=True);env=os.environ.copy();env.update({'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','PYTHONUTF8':'1'});limits={'seconds':300,'rss_gib':4,'minimum_free_gib':16}
control=guarded([sys.executable,'-X','utf8',str(root/'validate_peak_policy.py')],root,env,cache/'controls.log',limits)
assert control['exit_code']==0 and not control['guard_stop']
def run(indices):
 name='models-'+'-'.join(map(str,indices));r=guarded([sys.executable,'-X','utf8',str(root/'folded_peak_policy.py'),'--models',*map(str,indices),'--seconds','210'],root,env,cache/(name+'.log'),limits);return {'models':indices,**r}
records=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 for future in concurrent.futures.as_completed([pool.submit(run,m) for m in [[0,1],[2,3],[4,5],[6]]]):
  r=future.result();records.append(r);(root/'guard-report.json').write_text(json.dumps({'controls':control,'shards':records},indent=2)+'\n',encoding='utf-8');print({'shard_guard':r},flush=True)
