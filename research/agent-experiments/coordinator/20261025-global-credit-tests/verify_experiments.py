"""Read-only finite-experiment audit; deliberately not a proof checker."""
from pathlib import Path
import ast,hashlib,json,subprocess,sys
root=Path(__file__).resolve().parent;staged='--staged' in sys.argv
repo=next((p for p in root.parents if (p/'.git').exists()),None)
def read(p):
    if staged:
        assert repo is not None
        return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
m=json.loads(read(root/'artifacts.json'))
for rel,sha in m['files'].items():
    p=(root/rel).resolve();assert p.is_relative_to(root.resolve())
    assert hashlib.sha256(read(p)).hexdigest()==sha,rel
assert {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}==set(m['files'])|{'artifacts.json'}
assert not list(root.rglob('*.lean'))
summary=json.loads(read(root/'summary.json'));assert summary['new_kernel_verified_declarations']==0 and not summary['full_problem_solved']
for job in summary['jobs']:
    guard=json.loads(read(root/'work/evidence'/(job+'.guard.json')))
    assert guard['exit_code']==0 and guard['guard_stop'] is None,job
for source,out in summary['source_outputs'].items():
    ast.parse(read(root/'work'/source),filename=source)
    d=json.loads(read(root/'work'/out))
    assert d['finite_only'] and d['Lean_verified'] is False
    assert hashlib.sha256(read(root/'work'/source)).hexdigest()==d['source_sha256'],source
for name in ['global-block-search.json','global-block-dominating-search.json','global-block-incremental-search.json']:
    d=json.loads(read(root/'work'/name));assert d['results'][-1]['solver_result']=='unknown'
learned=json.loads(read(root/'work/trained-global-block-rank.json'))
assert learned['training_unique_guarded']==106 and learned['heldout_unique_guarded']==375
assert not learned['training_exact_failure_onsets'] and len(learned['heldout_exact_failure_onsets'])==165
assert learned['quantization_scale']==8 and learned['best_training_step']==5000
summed=json.loads(read(root/'work/global-block-sum-search.json'))
assert [len(r['heldout_exact_failures']) for r in summed['results']]==[179,170,174,175]
assert all(not r['training_exact_failures'] for r in summed['results'])
for name in ['global-multiset-cone.json','global-boundary-length-cone.json']:
    d=json.loads(read(root/'work'/name));assert d['result']['status']==2 and not d['result'].get('exact_integer_certificate',False)
    assert d['controls']['two_event_cycle']['exact_integer_certificate']
rootdata=json.loads(read(root/'work/root-gap-potential.json'));w=rootdata['coordinatewise_nonnegative_potential_counterexample']
assert (w['T'],w['P'],w['elapsed'])==(0,4,0) and all(y>=x for x,y in zip(w['before'],w['after']))
physical=json.loads(read(root/'work/root-small-control.json'));assert physical['independent_physical_control'] and physical['all_centers_match']
assert physical['records'][0]['root_positions']==[-4] and physical['records'][2]['root_positions']==[-6,-5]
clock=json.loads(read(root/'work/empty-trace-renewal-clock.json'))
assert hashlib.sha256(read(root/'work/empty-free-262144.bin')).hexdigest()==clock['trace_sha256']
assert len(read(root/'work/empty-free-262144.bin'))==262144
assert max(r['best_clock_lower_bound'] for r in clock['periods'])==274
assert max(r['clock_lower_bound'] for r in clock['all_lags_at_selected_onsets'])==274
print(json.dumps({'pass':True,'staged_blobs':staged,'hashed_files':len(m['files']),
                  'new_kernel_verified_declarations':0,'full_problem_solved':False},indent=2))
