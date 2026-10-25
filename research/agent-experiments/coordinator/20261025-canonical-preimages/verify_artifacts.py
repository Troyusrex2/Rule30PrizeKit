"""Check archive bytes, proof provenance and scope; optionally actual index blobs."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent
repo=next(p for p in root.parents if (p/'.git').exists())
staged='--staged' in sys.argv
def read(p):
    if staged:return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
def obj(p):return json.loads(read(p))
m=obj(root/'artifacts.json');s=obj(root/'summary.json');w=root/'work'
assert set(m['files'])|{'artifacts.json'}=={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
for f,h in m['files'].items():
    raw=read(root/f);assert hashlib.sha256(raw).hexdigest()==h,f
    if f.endswith('.py'):ast.parse(raw,filename=f)
    if f.endswith('.json'):json.loads(raw)
assert s['prior_hashes_unchanged']==1024
assert s['new_uniform_finite_horizon_obstruction']
assert not any(s[k] for k in ['full_problem_solved','all_time_common_mode_found',
                             'EdgeObservable_refuted','new_prize_submission','new_catalog_PR'])
for name,count in [('Rule30PreimageResearch',49),('Rule30CanonicalPulseResearch',45)]:
    r=obj(w/'evidence'/name/'report.json');c=r['check']
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True} and not c['newAxioms']
    assert r['kit_commit']==s['kit_commit'] and r['checker_unchanged']
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert len(c['headlines'])==3 and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    source=read(w/(name+'.lean'))
    assert r['source_sha256']==hashlib.sha256(source).hexdigest()
    assert not re.search(rb'\b(sorry|axiom|native_decide|bv_decide)\b|decide\s*\+native|skipKernel',source)
p=obj(w/'backward-fields.json');assert p['pairs']==190 and p['late_all_finite_failures']==0
assert p['late_subset_common_failures']==0 and p['finite_horizon_only'] and not p['Lean_verified']
d=obj(w/'dyadic-pulse-checked.json');assert len(d['records'])==11 and not d['Lean_verified']
assert all(not r['current_h_carries_canonical_left_edge'] for r in d['records'])
assert all(r['first_W_failure_through_cap']>r['guaranteed_disjoint_cone_horizon'] for r in d['records'])
a=obj(w/'independent-pulse-controls.json')
assert a['pass'] and a['scalar_canonical_cells']==17157 and a['scalar_mode_timesteps']==325
assert a['exhaustive_small_preimages']==32512 and a['known_seed_controls']==7
assert a['local_truth_assignments']==256 and not a['Lean_proof_premise']
for label in s['passed_guarded_jobs']:
    g=obj(w/'evidence'/(label+'.guard.json'))
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3
    assert g['minimum_system_available_bytes']>=2*1024**3
g=obj(w/'evidence/dyadic_pulse_probe.guard.json')
assert g['exit_code']==1 and g['guard_stop'] is None
for path in root.rglob('*'):
    if not path.is_file():continue
    raw=read(path)
    assert not re.search(rb'oauth_token=[a-zA-Z0-9-]+|AKIA[0-9A-Z]{16}|gh[pousr]_[A-Za-z0-9]{30,}',raw),str(path)
print(json.dumps({'pass':True,'actual_staged_blobs':staged,'selected_hashes':len(m['files']),
                  'uniform_obstruction_verified':True,'full_problem_solved':False}))
