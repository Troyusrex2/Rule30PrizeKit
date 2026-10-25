"""Read-only archive audit, including actual staged blobs when requested.
Byte hashes and metadata checks do not substitute for Lean kernel replay.
"""
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
assert len(summary['modules'])==7 and summary['new_owned_replays']==199 and not summary['full_problem_solved']
for record in summary['modules']:
    name=record['module'];report=json.loads(read(root/'work/evidence'/name/'report.json'))
    guard=json.loads(read(root/'work/evidence'/name/'guard.json'))
    assert report['check']['verdict']=='pass' and report['check']['replay']['ok'] and not report['check']['newAxioms']
    assert report['check']['replay']['constants']==record['constants']
    assert all(h['ok'] for h in report['check']['headlines'])
    assert hashlib.sha256(read(root/'work'/(name+'.lean'))).hexdigest()==report['source_sha256']
    assert report['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert report['checker_unchanged'] and report['kit_commit']=='3eca23c0a9fa6b153313655e6d51835406c2d06e'
    assert guard['exit_code']==0 and guard['guard_stop'] is None
for p in (root/'work/evidence').glob('*.guard.json'):
    guard=json.loads(read(p));assert guard['exit_code']==0 and guard['guard_stop'] is None,p
front=json.loads(read(root/'work/greedy-front.json'))
assert front['case_count']==99 and all(r['first_hit'] is not None for r in front['records'])
ether=json.loads(read(root/'work/ether_greedy_cycles.json'))
assert len(ether['records'])==93 and all(r['cycle_displacement']==0 for r in ether['records'])
cycles=json.loads(read(root/'work/language-filtered-cycles.json'))
assert cycles['best']['black']==6 and cycles['best']['period']==28
for w in cycles['forbidden_words']:
    assert w not in cycles['best']['prefix_bits']
refined=json.loads(read(root/'work/inverse-refined-candidate.json'))
assert [(r['requested_free_prefix'],r['result']) for r in refined['records']]==[(32,'sat'),(40,'sat'),(48,'unsat')]
assert all(r.get('independent_physical_replay') for r in refined['records'] if r['result']=='sat')
print(json.dumps({'pass':True,'staged_blobs':staged,'hashed_files':len(manifest['files']),
                  'new_owned_replays':199,'full_problem_solved':False},indent=2))
