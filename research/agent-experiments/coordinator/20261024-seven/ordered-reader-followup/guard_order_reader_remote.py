"""Guard the owned CUDA reader training job; no system settings are changed."""
import hashlib,json,os,sys
from pathlib import Path
root=Path(__file__).resolve().parent;workerroot=Path.home()/'Rule30-offload';sys.path.insert(0,str(workerroot/'_cache/payload'))
from worker import guarded
assert (root/'OWNER.txt').read_text().strip()=='Rule30 ordered recurrent rank reader; 2026-10-25'
manifest=json.loads((root/'sources.json').read_text())
for n,h in manifest.items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h,n
cache=root/'_cache';cache.mkdir(exist_ok=True);env=os.environ.copy();env.update({'OMP_NUM_THREADS':'4','OPENBLAS_NUM_THREADS':'1','PYTHONUTF8':'1'})
r=guarded([sys.executable,'-X','utf8',str(root/'train_ordered_rank_reader.py'),'--architecture','relu','--seconds','165'],root,env,cache/'relu-training.log',{'seconds':300,'rss_gib':8,'minimum_free_gib':16})
(root/'guard-report.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print({'training_guard':r},flush=True)
if r['exit_code'] or r['guard_stop']:raise RuntimeError('Owned recurrent reader job stopped; inspect its log')
