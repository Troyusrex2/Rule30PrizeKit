"""Guard two owned CUDA discovery jobs, preserving separate source/results."""
import hashlib,json,os,sys
from pathlib import Path
root=Path(__file__).resolve().parent;workerroot=Path.home()/'Rule30-offload';sys.path.insert(0,str(workerroot/'_cache/payload'))
from worker import guarded
assert (root/'OWNER.txt').read_text().strip()=='Rule30 terminal-aware ordered rank reader v2; 2026-10-25'
manifest=json.loads((root/'sources.json').read_text())
for n,h in manifest.items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h,n
cache=root/'_cache';cache.mkdir(exist_ok=True);env=os.environ.copy();env.update({'OMP_NUM_THREADS':'4','OPENBLAS_NUM_THREADS':'1','PYTHONUTF8':'1'})
limits={'seconds':300,'rss_gib':8,'minimum_free_gib':16}
control=guarded([sys.executable,'-X','utf8',str(root/'validate_ordered_reader_v2.py')],root,env,cache/'architecture-controls.log',limits)
if control['exit_code'] or control['guard_stop']:raise RuntimeError('Architecture controls failed')
records=[]
for architecture in ['relu','gru']:
 r=guarded([sys.executable,'-X','utf8',str(root/'train_ordered_rank_reader.py'),'--architecture',architecture,'--seconds','165','--epochs','4000'],root,env,cache/(architecture+'-training.log'),limits)
 records.append({'architecture':architecture,**r})
 (root/'guard-report.json').write_text(json.dumps({'controls':control,'training':records},indent=2)+'\n',encoding='utf-8')
 print({'architecture':architecture,'training_guard':r},flush=True)
 if r['exit_code'] or r['guard_stop']:raise RuntimeError('Owned recurrent reader job stopped; inspect its log')
