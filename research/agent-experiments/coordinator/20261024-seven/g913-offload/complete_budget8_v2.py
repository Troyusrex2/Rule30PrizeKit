"""Complete only the corrected join after all immutable leaves pass replay."""
import hashlib,json,subprocess,sys,time
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')
root=Path.home()/'Rule30-offload';control=root/'_cache/budget8-c600';progress=root/'results/budget8-c600/progress.json'
start=time.monotonic();last=-1
while True:
    data=json.loads(progress.read_text(encoding='utf-8'))
    if data['failed']:raise RuntimeError('A leaf failed; do not assemble')
    n=len(data['completed'])
    if n!=last:print({'completed_leaf_replays':n,'required':404},flush=True);last=n
    if n==404:break
    if time.monotonic()-start>3600:raise TimeoutError('Leaf batch still incomplete; safe to resume later')
    time.sleep(5)
manifest=json.loads((control/'batch-manifest.json').read_text(encoding='utf-8'))
assert len(manifest['modules'])==404
for rec in manifest['modules']:
    source=control/rec['source'];digest=hashlib.sha256(source.read_bytes()).hexdigest()
    r=json.loads((root/'results/budget8-c600'/rec['module']/'report.json').read_text(encoding='utf-8'))
    assert digest==manifest['files'][rec['source']]==r['source_sha256']
    assert r['check']['verdict']=='pass' and r['check']['replay']['ok'] and not r['check']['newAxioms']
    assert all(h['ok'] for h in r['check']['headlines'])
print({'all_404_exact_sources_individually_replayed':True,'stage':'corrected_join'},flush=True)
subprocess.run([sys.executable,'-X','utf8',str(root/'_cache/check_one.py'),'--module','Rule30GoldenBudget8C600V2Research',
    '--headlines','checked','minimum_nine','no_golden_eight'],check=True)
print({'corrected_budget8_certificate_completed':True,'full_prize_problem_solved':False},flush=True)
