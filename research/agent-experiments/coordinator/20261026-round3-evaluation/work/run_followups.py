from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
import json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
tasks=['right_admissibility','wiki_closed_profile','swarm_phase_test','sanity_holdout','cedar_pilot','backend_holdout']
start=time.monotonic();records=[]
def job(task):
    print(json.dumps({'task':task,'state':'starting'}),flush=True)
    r=subprocess.run([sys.executable,'-X','utf8','-B',str(ROOT/'guard.py'),task+'.py'],cwd=ROOT,capture_output=True)
    (ROOT/('followup-'+task+'.log')).write_bytes(r.stdout+r.stderr)
    result={'task':task,'exit_code':r.returncode}
    print(json.dumps(result),flush=True)
    return result
with ThreadPoolExecutor(max_workers=2) as pool:
    for future in as_completed([pool.submit(job,t) for t in tasks]):records.append(future.result())
report={'tasks':records,'all_exited_zero':all(r['exit_code']==0 for r in records),
        'seconds':round(time.monotonic()-start,3),'finite_only':True,'Lean_verified':False}
(ROOT/'followup-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
