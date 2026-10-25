"""Read-only byte and proof-metadata audit; hashes do not replace kernel replay."""
from pathlib import Path
import hashlib,json,sys,subprocess
root=Path(__file__).resolve().parent
staged='--staged' in sys.argv
repo=next((p for p in root.parents if (p/'.git').exists()),None)
def read(p):
    if staged:
        assert repo is not None
        return subprocess.run(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo,check=True,capture_output=True).stdout
    return p.read_bytes()
manifest=json.loads(read(root/'artifacts.json'))
for rel,sha in manifest['files'].items():
    p=(root/rel).resolve()
    assert p.is_relative_to(root.resolve())
    assert hashlib.sha256(read(p)).hexdigest()==sha,rel
assert {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}==set(manifest['files'])|{'artifacts.json'}
responses=0;artifacts=0
for folder in (root/'work/snapshots').iterdir():
    m=json.loads(read(folder/'manifest.json'))
    assert m['response_id']==folder.name and (folder/'READY').is_file()
    for a in m['artifacts']:
        assert hashlib.sha256(read(folder/a['path'])).hexdigest()==a['sha256'],(folder.name,a['path'])
        artifacts+=1
    responses+=1
summary=json.loads(read(root/'proof-summary.json'))
assert len(summary['modules'])==7 and summary['new_owned_replays']==210 and summary['full_problem_solved'] is False
for record in summary['modules']:
    name=record['module'];report=json.loads(read(root/'work/evidence'/name/'report.json'))
    guard=json.loads(read(root/'work/evidence'/name/'guard.json'))
    assert report['check']['verdict']=='pass' and report['check']['replay']['ok'] and not report['check']['newAxioms']
    assert report['check']['replay']['constants']==record['constants']
    assert all(h['ok'] for h in report['check']['headlines'])
    assert hashlib.sha256(read(root/'work'/(name+'.lean'))).hexdigest()==report['source_sha256']
    assert guard['exit_code']==0 and guard['guard_stop'] is None
assert responses==7
cedar=json.loads(read(root/'work/evidence/cedar/kernel_report.json'))
assert cedar['check']['verdict']=='pass' and cedar['check']['replay']=={'constants':44,'ok':True}
rank30=json.loads(read(root/'work/conservation-rule30-m9.json'))
rank184=json.loads(read(root/'work/conservation-rule184-m5.json'))
assert len(rank30['results'])==27 and all(r['certified_only_trivial_conserved_densities'] for r in rank30['results'])
assert len(rank184['results'])==15 and all(r['rank_mod_p_lower_bound']==r['trivial_rank_upper_bound']-1 for r in rank184['results'])
background=json.loads(read(root/'work/backend-background-reader.stdout.log'))
assert background['sink_cost_certificate']['all_equalities_certified']
print(json.dumps({'pass':True,'staged_blobs':staged,'hashed_files':len(manifest['files']),
                  'responses':responses,'received_artifacts':artifacts,'new_owned_replays':210,'incoming_cedar_replay':44},indent=2))
