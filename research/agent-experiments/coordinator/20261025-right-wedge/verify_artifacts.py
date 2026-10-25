from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent;repo=next(p for p in root.parents if (p/'.git').exists())
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
assert s['prior_hashes_unchanged']==1065 and not s['full_problem_solved']
assert not s['all_width_band_conjecture_proved'] and not s['new_prize_submission']
for name,count,heads in [('Rule30VacuumGaugeResearch',46,2),('Rule30RightWedgeResearch',49,3)]:
    r=obj(w/'evidence'/name/'report.json');c=r['check']
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True} and not c['newAxioms']
    assert r['kit_commit']==s['kit_commit'] and r['checker_unchanged']
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    assert r['source_sha256']==hashlib.sha256(read(w/(name+'.lean'))).hexdigest()
r=obj(w/'catalog-evidence/report.json');c=r['check'];source=read(w/'Rule30CommonGauge.lean')
assert r['source_sha256']==hashlib.sha256(source).hexdigest()=='748cc6a15913ab9362616b52c7c3890b4f5e3be9ef3dcc5477cbac5c53b9b80a'
assert c['verdict']=='pass' and c['replay']=={'constants':95,'ok':True} and not c['newAxioms']
assert len(c['headlines'])==4 and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
assert r['checker_unchanged'] and r['kit_commit']==s['kit_commit']
assert not re.search(rb'\b(sorry|axiom|native_decide|bv_decide)\b|decide\s*\+native|skipKernel|Mathlib',source)
pr=obj(w/'catalog-pr-readback.json')
assert pr['pass'] and pr['body_exact'] and pr['number']==28 and pr['changed_files']==3 and not pr['merged']
assert pr['head_sha']=='24fe825edf60abbad7d7373bfbfca0af68cf0f31'
g=obj(w/'independent-gap-controls.json');assert g['pass'] and g['initial_pairs']==87380
assert g['distance_implications']==128584 and g['initial_subset_classifications']==1012
assert g['independent_scalar_timesteps']==2708 and not g['Lean_proof_premise']
l=obj(w/'local-factors.json');assert [f['table_integer'] for f in l['factors']]==[0,204,240]
assert l['subset_propagation_counterexample'] is not None and not l['Lean_verified']
e=obj(w/'exterior-lift-probe.json');assert e['pairs']==276 and e['max_first_cover']==11
assert not e['Lean_verified'] and not e['all_time_lifting_refuted']
b=obj(w/'escaping-band-probe.json');assert len(b['widths'])==13 and not b['cycle_verified_survivors']
assert sum(x['cases'] for x in b['widths'])==4610 and b['all_age_gaps_covered_at_each_tested_width']
assert not b['Lean_verified']
b=obj(w/'independent-band-controls.json');assert b['pass'] and b['small_physical_cases']==114
assert b['nonzero_initial_subset_modes']==b['rejected_modes']==832
assert b['known_escaping_noncanonical_timesteps']==65 and not b['Lean_proof_premise']
for name,n,ys,initial in [('prefix-class-probe',22098,True,True),('prefix-a-only-probe',43688,False,True),
                          ('prefix-unrestricted-probe',43688,False,False)]:
    p=obj(w/(name+'.json'));assert p['cases']==n and p['low_class_replacement_counterexample'] is None
    assert p['older_low_class_zero_required'] and p['younger_low_class_zero_required']==ys
    assert p['initial_subset_required']==initial and not p['Lean_verified']
p=obj(w/'left-edge-nonlift-probe.json');assert len(p['records'])==7 and not p['Lean_verified']
assert all(r['carries_canonical_left_edge'] and r['common_W_through_H'] and
           r['right_exterior_phase_zero_through_H'] and not r['zero_center_assumed'] for r in p['records'])
assert any(any(r['center_observations_through_H']) for r in p['records'])
for label in s['passed_guarded_jobs']:
    g=obj(w/'evidence'/(label+'.guard.json'));assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3
    assert g['minimum_system_available_bytes']>=2*1024**3
for path in root.rglob('*'):
    if path.is_file():assert not re.search(rb'oauth_token=[a-zA-Z0-9-]+|AKIA[0-9A-Z]{16}|gh[pousr]_[A-Za-z0-9]{30,}',read(path)),str(path)
print(json.dumps({'pass':True,'actual_staged_blobs':staged,'selected_hashes':len(m['files']),
                  'PR':28,'full_problem_solved':False,'band_conjecture_proved':False}))
