from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent;repo=next(p for p in root.parents if (p/'.git').exists())
staged='--staged' in sys.argv
def read(p):
    if staged:return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
def obj(p):return json.loads(read(p))
m=obj(root/'artifacts.json');s=obj(root/'summary.json');w=root/'work';essay=w/'essay-combined'
assert set(m['files'])|{'artifacts.json'}=={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
for f,h in m['files'].items():
    raw=read(root/f);assert hashlib.sha256(raw).hexdigest()==h,f
    if f.endswith('.py'):ast.parse(raw,filename=f)
    if f.endswith('.json'):json.loads(raw)
assert s['prior_hashes_unchanged']==1134 and s['canonical_all_width_band_escape_proved']
assert not any(s[k] for k in ['full_problem_solved','arbitrary_three_bit_conjecture_proved',
                             'full_notebook_fresh_verified','new_prize_submission'])
for path,source,count,heads in [(w/'evidence/Rule30BandEscapeResearch/report.json',w/'Rule30BandEscapeResearch.lean',52,3),
                              (w/'evidence/Rule30Submission/report.json',w/'Rule30Submission.lean',164,7),
                              (w/'catalog-evidence/report.json',w/'Rule30CommonGauge.lean',164,7)]:
    r=obj(path);c=r['check']
    assert r['source_sha256']==hashlib.sha256(read(source)).hexdigest()
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True} and not c['newAxioms']
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    assert r['kit_commit']==s['kit_commit'] and r['checker_unchanged']
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert not re.search(rb'\b(sorry|axiom|native_decide|bv_decide)\b|decide\s*\+native|skipKernel',read(source))
assert hashlib.sha256(read(w/'Rule30CommonGauge.lean')).hexdigest()=='4a397a0d6699aa1632b58f4d1d7e74e8a83ebd15471065a6d056b1a15470759e'
src=read(essay/'Rule30Submission.lean');assert src==read(w/'Rule30Submission.lean')
assert src.startswith(b'import Rule30PrizeKit\n')
assert hashlib.sha256(src).hexdigest()=='14d953c5c4eb3aa15f42dabd4702f6bed8500de18b1e7b65600a7ef28233c8f5'
p=obj(essay/'preflight.json');assert p['standalone_CLI_verified'] and p['standalone_replayed_declarations']==164
assert not p['notebook_fresh_verified'] and p['input_cells']==7
p=obj(essay/'preview-packaging.json');assert p['packagingPass'] and p['sourceRoundTrip'] and p['sourceIconized']
assert p['sourceSHA256']==hashlib.sha256(src).hexdigest() and not p['proofCellsExecuted'] and not p['freshNotebookVerified']
assert p['notebookSHA256']==hashlib.sha256(read(essay/'common-gauge-preview-unevaluated.nb')).hexdigest()
assert not (essay/'common-gauge-essay.nb').exists()
g=obj(essay/'build-launch-state.json');assert g['state']=='not_started_insufficient_memory'
assert g['available_bytes']<g['required_available_bytes']==10500000000 and not g['fresh_notebook_verified']
p=obj(essay/'exploration-controls.json');assert p['pass'] and p['finiteGapControl']==[0,1]
assert p['resetPrefix']==[1,0,0,0,0] and not p['proofCellsExecuted'] and not p['freshNotebookVerified']
pr=obj(w/'catalog-pr-readback.json');assert pr['pass'] and pr['number']==28 and pr['body_exact'] and pr['changed_files']==3
assert pr['head_sha']=='b75e62d12ed804bbc81b85a3814f5ff0b242a335'
p=obj(w/'independent-escape-controls.json');assert p['pass'] and not p['Lean_proof_premise']
assert p['physical_coordinate_D_steps']==5280 and p['initial_band_states']==502
assert p['arbitrary_b_transition_controls']==120903 and p['noncanonical_escaping_control_timesteps']==65
p=obj(w/'drop-w-probe.json');assert p['cases']==43688 and not p['W_required'] and not p['initial_subset_required']
assert p['low_class_replacement_counterexample'] is None and not p['Lean_verified']
p=obj(w/'free-b-control.json');assert len(p['records'])==5 and all(r['verdict']=='unsat' for r in p['records'])
assert not p['Lean_verified']
for label in s['passed_guarded_jobs']:
    g=obj(w/'evidence'/(label+'.guard.json'));assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3
    assert g['minimum_system_available_bytes']>=2*1024**3
g=obj(w/'evidence/build_combined_essay.guard.json');assert g['exit_code']==3 and g['guard_stop'] is None
for path in root.rglob('*'):
    if path.is_file():assert not re.search(rb'oauth_token=[a-zA-Z0-9-]+|AKIA[0-9A-Z]{16}|gh[pousr]_[A-Za-z0-9]{30,}',read(path)),str(path)
print(json.dumps({'pass':True,'actual_staged_blobs':staged,'selected_hashes':len(m['files']),
                  'canonical_all_width_band_escape_proved':True,'full_problem_solved':False,'full_notebook_verified':False}))
