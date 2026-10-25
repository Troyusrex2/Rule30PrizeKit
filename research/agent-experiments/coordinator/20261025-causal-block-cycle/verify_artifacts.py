"""Read-only byte/metadata audit; --staged reads actual index blobs."""
from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parent;staged='--staged' in sys.argv
repo=next((p for p in root.parents if (p/'.git').exists()),None)
def read(p):
    if staged:
        assert repo is not None
        return subprocess.run(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo,check=True,capture_output=True).stdout
    return p.read_bytes()
manifest=json.loads(read(root/'artifacts.json'))
for rel,sha in manifest['files'].items():
    p=(root/rel).resolve();assert p.is_relative_to(root.resolve())
    assert hashlib.sha256(read(p)).hexdigest()==sha,rel
assert {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}==set(manifest['files'])|{'artifacts.json'}
summary=json.loads(read(root/'proof-summary.json'))
assert summary['new_owned_replays']==258 and not summary['full_problem_solved']
assert len(summary['modules'])==2
for record in summary['modules']:
    name=record['module'];report=json.loads(read(root/'work/evidence'/name/'report.json'))
    guard=json.loads(read(root/'work/evidence'/name/'guard.json'))
    assert report['check']['verdict']=='pass' and report['check']['replay']=={'ok':True,'constants':record['constants']}
    assert not report['check']['newAxioms'] and all(h['ok'] for h in report['check']['headlines'])
    assert report['source_sha256']==hashlib.sha256(read(root/'work'/(name+'.lean'))).hexdigest()
    assert report['kit_commit']=='3eca23c0a9fa6b153313655e6d51835406c2d06e' and report['checker_unchanged']
    assert report['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert guard['exit_code']==0 and guard['guard_stop'] is None
results=json.loads(read(root/'work/block-rank-distinct-onsets.json'))
assert results['distinct_onsets']==4096 and results['results'][0]['solver_result']=='sat'
assert results['results'][0]['heldout']['global_DM_failures']==122
assert results['results'][1]['solver_result']=='unsat' and len(results['results'][1]['unsat_core'])==8
assert len(json.loads(read(root/'work/block-cycle-witnesses.json'))['records'])==8
print(json.dumps({'pass':True,'staged_blobs':staged,'hashed_files':len(manifest['files']),
                  'new_owned_replays':258,'full_problem_solved':False},indent=2))
