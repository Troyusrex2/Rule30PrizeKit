"""Guard the owned V3 warm-start experiment and independent test audit."""
import hashlib,json,os,sys
from pathlib import Path
root=Path(__file__).resolve().parent;workerroot=Path.home()/'Rule30-offload';sys.path.insert(0,str(workerroot/'_cache/payload'))
from worker import guarded
assert (root/'OWNER.txt').read_text().strip()=='Rule30 terminal-aware ordered rank reader v3; 2026-10-25'
for n,h in json.loads((root/'sources.json').read_text()).items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h,n
old=workerroot/'research/ordered-rank-reader-v2-20261025/results';warm=root/'warmstart';warm.mkdir(exist_ok=True)
architecture='relu';origin=old/(architecture+'-reader-weights.pt');oldreport=json.loads((old/(architecture+'-reader-report.json')).read_text())
raw=origin.read_bytes();assert hashlib.sha256(raw).hexdigest()==oldreport['weight_sha256'];(warm/('v2-'+architecture+'-reader-weights.pt')).write_bytes(raw)
(warm/'provenance.json').write_text(json.dumps({'v2_report_sha256':hashlib.sha256((old/(architecture+'-reader-report.json')).read_bytes()).hexdigest(),'weight_sha256':hashlib.sha256(raw).hexdigest()},indent=2)+'\n',encoding='utf-8')
cache=root/'_cache';cache.mkdir(exist_ok=True);env=os.environ.copy();env.update({'OMP_NUM_THREADS':'4','OPENBLAS_NUM_THREADS':'1','PYTHONUTF8':'1'});limits={'seconds':300,'rss_gib':8,'minimum_free_gib':16};records=[]
for name,argv in [('controls',[sys.executable,'-X','utf8',str(root/'validate_ordered_reader_v2.py')]),('training',[sys.executable,'-X','utf8',str(root/'train_ordered_rank_reader.py'),'--architecture',architecture,'--seconds','165','--epochs','4000']),('test',[sys.executable,'-X','utf8',str(root/'audit_ordered_reader_v3.py'),'--architecture',architecture])]:
 r=guarded(argv,root,env,cache/(name+'.log'),limits);records.append({'stage':name,**r});(root/'guard-report.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8');print({'stage':name,'guard':r},flush=True)
 if r['exit_code'] or r['guard_stop']:raise RuntimeError('V3 stage failed: '+name)
