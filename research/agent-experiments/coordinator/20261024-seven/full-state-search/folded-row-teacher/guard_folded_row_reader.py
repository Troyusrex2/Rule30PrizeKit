"""Guard the new full-configuration reader, not an anti-diagonal retry."""
import hashlib,json,os,sys
from pathlib import Path
root=Path(__file__).resolve().parent;sys.path.insert(0,str(Path.home()/'Rule30-offload/_cache/payload'))
from worker import guarded
assert (root/'OWNER.txt').read_text().strip()=='Rule30 supervised folded spatial row reader; 2026-10-25'
for n,h in json.loads((root/'sources.json').read_text()).items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h,n
cache=root/'_cache';cache.mkdir(exist_ok=True);env=os.environ.copy();env.update({'OMP_NUM_THREADS':'4','OPENBLAS_NUM_THREADS':'1','PYTHONUTF8':'1'});limits={'seconds':300,'rss_gib':8,'minimum_free_gib':16};records=[]
for name,args in [('controls',['validate_ordered_reader_v2.py']),('training',['train_ordered_rank_reader.py','--architecture','relu','--seconds','165','--epochs','4000']),('test',['audit_ordered_reader_v3.py','--architecture','relu'])]:
 r=guarded([sys.executable,'-X','utf8',str(root/args[0]),*args[1:]],root,env,cache/(name+'.log'),limits);records.append({'stage':name,**r});(root/'guard-report.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8');print({'stage':name,'guard':r},flush=True)
 if r['exit_code'] or r['guard_stop']:raise RuntimeError('Full-row reader stage failed: '+name)
