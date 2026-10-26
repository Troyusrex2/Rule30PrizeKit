"""Finish the untested cases with a real per-owned-child wall cap.
The outer 300s/8GiB/2GiB guard remains unchanged. A killed case is unknown.
"""
from pathlib import Path
import json,os,subprocess,sys,time
import psutil
root=Path(__file__).resolve().parent
old=json.loads((root/'context-rank-partial.json').read_bytes())['reports']
reports=list(old)
for K,moment in [(2,True),(3,False),(3,True),(4,False),(4,True)]:
    start=time.monotonic();log=root/'evidence'/f'context-case-{K}-{int(moment)}.log'
    with log.open('w',encoding='utf-8') as f:
        p=subprocess.Popen([sys.executable,'-B',str(root/'context_rank.py'),str(K),str(int(moment))],
                           cwd=root,stdout=f,stderr=subprocess.STDOUT,env=dict(os.environ))
        try:
            p.wait(timeout=20)
            if p.returncode:rec={'context':K,'first_moment':moment,'status':'process_failed','exit_code':p.returncode}
            else:rec=json.loads((root/f'context-rank-{K}-{int(moment)}.json').read_bytes())['reports'][0]
        except subprocess.TimeoutExpired:
            owned=psutil.Process(p.pid)
            for child in reversed(owned.children(recursive=True)):
                try:child.kill()
                except psutil.NoSuchProcess:pass
            try:owned.kill()
            except psutil.NoSuchProcess:pass
            p.wait(timeout=5)
            rec={'context':K,'first_moment':moment,'status':'unknown_wall_cap','case_wall_cap_seconds':20,
                 'seconds':round(time.monotonic()-start,3)}
    reports.append(rec);print(json.dumps(rec),flush=True)
    (root/'context-rank-complete.json').write_text(json.dumps({'reports':reports,
        'original_job_guard_stop':'wall_time','Lean_verified':False,'sink_separation_proved':False,
        'full_problem_solved':False},indent=2)+'\n',encoding='utf-8')
    if rec['status']=='sat':break
