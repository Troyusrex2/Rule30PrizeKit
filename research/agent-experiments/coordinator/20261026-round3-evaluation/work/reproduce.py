"""Replay numerical responses only inside owned copies, under an outer guard."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
TASKS={
 'sanity':('r30-codex-sanity-20261026T005702Z-9cfc0376-v01','src/experiment.py',[],'root'),
 'backend-runs':('r30-coinailyzer-backend-20261026T005537Z-dec034cb-v01','src/runs.py',['15'],'root'),
 'backend-probe':('r30-coinailyzer-backend-20261026T005537Z-dec034cb-v01','src/probe.py',['14'],'root'),
 'photo-gate':('r30-photograde-20261026T005626Z-1de68195-v01','src/restrike.py',['F001'],'root'),
 'photo-runs':('r30-photograde-20261026T005626Z-1de68195-v01','src/restrike.py',['F002'],'root'),
 'photo-control':('r30-photograde-20261026T005626Z-1de68195-v01','src/restrike.py',['F002C'],'root'),
 'swarm-agreement':('r30-coinailyzer-swarm-20261026T005722Z-a7c78bac-v01','src/dyadic_centercol.py',[],'root'),
 'swarm-slope':('r30-coinailyzer-swarm-20261026T005722Z-a7c78bac-v01','src/exact_slope.py',[],'root'),
 'ml-sideways':('r30-coinailyzer-mlcontract-20261026T005856Z-253cdbda-v01','src/sideways_sat_count.py',[],'src'),
 'ml-control':('r30-coinailyzer-mlcontract-20261026T005856Z-253cdbda-v01','src/control_and_sweep.py',[],'src'),
 'ml-transient':('r30-coinailyzer-mlcontract-20261026T005856Z-253cdbda-v01','src/transient_test.py',[],'src'),
 'ml-density':('r30-coinailyzer-mlcontract-20261026T005856Z-253cdbda-v01','src/defect_depth_profile.py',[],'src'),
 'wiki-core':('r30-coinailyzer-wiki-20261026T005537Z-e656e7b7-v01','src/coupled_core.py',[],'root'),
 'wiki-clock':('r30-coinailyzer-wiki-20261026T005537Z-e656e7b7-v01','src/geometric_clock.py',[],'root'),
 'wiki-density':('r30-coinailyzer-wiki-20261026T005537Z-e656e7b7-v01','src/density_floor.py',['120'],'root'),
 'wiki-94':('r30-coinailyzer-wiki-20261026T005537Z-e656e7b7-v01','src/verify_94.py',[],'root'),
 'wiki-sweep':('r30-coinailyzer-wiki-20261026T005537Z-e656e7b7-v01','src/sweep.py',['1200'],'root'),
 'wiki-achievable':('r30-coinailyzer-wiki-20261026T005537Z-e656e7b7-v01','src/achievable_slips.py',['16','70'],'root'),
 'wiki-gas':('r30-coinailyzer-wiki-20261026T005537Z-e656e7b7-v01','src/slip_gas.py',['1200'],'root')}
p=argparse.ArgumentParser();p.add_argument('task',choices=TASKS);a=p.parse_args()
folder,source,argv,where=TASKS[a.task]
snapshot=ROOT/'snapshots'/folder
manifest=json.loads((snapshot/'manifest.json').read_text(encoding='utf-8-sig'))
for item in manifest['artifacts']:
 assert hashlib.sha256((snapshot/item['path']).read_bytes()).hexdigest()==item['sha256']
run=ROOT/'runs'/a.task
assert not run.exists(), 'Use a new run label rather than overwriting evidence'
shutil.copytree(snapshot,run)
if a.task=='sanity':argv=[str(run/'reproduced-output')]
start=time.monotonic()
result=subprocess.run([sys.executable,'-X','utf8','-B',str(run/source),*argv],
 cwd=run/where if where!='root' else run,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(run/'reproduction.log').write_bytes(result.stdout)
record={'task':a.task,'source_sha256':hashlib.sha256((run/source).read_bytes()).hexdigest(),
 'exit_code':result.returncode,'seconds':round(time.monotonic()-start,3),
 'finite_only':True,'Lean_verified':False,'full_problem_solved':False}
(run/'reproduction.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
print(result.stdout.decode('utf-8',errors='replace')[-3500:],flush=True)
result.check_returncode()
