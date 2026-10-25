"""Guard four independent numerical shards in a named research workspace."""
import hashlib,json,os,sys,time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
root=Path(__file__).resolve().parent;workerroot=Path.home()/'Rule30-offload';sys.path.insert(0,str(workerroot/'_cache/payload'))
from worker import guarded
assert (root/'OWNER.txt').read_text().strip()=='Rule30 uniform spatial reader search; 2026-10-25'
manifest=json.loads((root/'sources.json').read_text())
for n,digest in manifest.items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==digest,n
ranges=[(0,16384),(16384,32768),(32768,49152),(49152,65536)];start=time.monotonic();env=os.environ.copy();env.update({'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','MKL_NUM_THREADS':'1','PYTHONUTF8':'1'})
limits={'seconds':300,'rss_gib':4,'minimum_free_gib':16};logs=root/'_cache';logs.mkdir(exist_ok=True)
def read(a,b):
 p=root/'results'/f'two-state-{a:05d}-{b:05d}.json'
 return json.loads(p.read_text()) if p.exists() else {'next_code':a,'complete':False}
for roundnum in range(10):
 pending=[(a,b) for a,b in ranges if not read(a,b)['complete']]
 if not pending or list((root/'results').glob('candidate-*.json')):break
 def job(ab):
  a,b=ab
  return guarded([sys.executable,'-X','utf8',str(root/'enumerate_two_state_readers.py'),'--start',str(a),'--end',str(b),'--seconds','210'],root,env,logs/f'round{roundnum:02d}-{a:05d}.log',limits)
 with ThreadPoolExecutor(max_workers=4) as pool:reports=list(pool.map(job,pending))
 summary={'round':roundnum,'elapsed':round(time.monotonic()-start,3),'shards':[{k:r.get(k) for k in ['range','next_code','complete','status_counts','unknown_codes','exact_candidate_codes']} for r in [read(a,b) for a,b in ranges]],'guards':reports,'full_problem_solved':False}
 (root/'progress.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8');print(summary,flush=True)
 if any(r['exit_code'] or r['guard_stop'] for r in reports):raise RuntimeError('A guarded reader shard stopped; inspect owned logs before resuming')
 if time.monotonic()-start>2400:break
print({'reader_batch_finished':True,'all_code_ranges_complete':all(read(a,b)['complete'] for a,b in ranges),'candidate_files':[p.name for p in (root/'results').glob('candidate-*.json')],'full_problem_solved':False},flush=True)
