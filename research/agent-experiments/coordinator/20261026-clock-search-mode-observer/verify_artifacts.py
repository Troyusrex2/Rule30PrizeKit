from pathlib import Path
import argparse,hashlib,json,re,subprocess,tarfile,io
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
r=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=r,text=True).strip())
prefix=r.relative_to(repo).as_posix()
def read(n):
    return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (r/n).read_bytes()
def data(n):return json.loads(read(n))
m=data('artifacts.json')['files']
for n,h in m.items():assert hashlib.sha256(read(n)).hexdigest()==h,n
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
official=subprocess.check_output(['git','archive','--format=tar',pin],cwd=repo)
with tarfile.open(fileobj=io.BytesIO(official),mode='r:') as t:
    manifest=data('work/source-manifest.json');assert manifest['pin']==pin
    assert len(manifest['files'])==267
    for n,h in manifest['files'].items():assert hashlib.sha256(t.extractfile(n).read()).hexdigest()==h,n
    assert hashlib.sha256(t.extractfile('Check.lean').read()).hexdigest()==checker
inv=data('work/final-pin-audit.json')
assert data('work/environment.json')['kit']['commit']==pin
assert inv['passed'] and inv['kit_commit']==pin and inv['module_count']==41
assert inv['total_replayed_declarations']==1068 and inv['new_module_declarations']==97
new={'Rule30CubicAlgebraResearch':32,'Rule30ClockSearchResearch':36,'Rule30ClockModeResearch':29}
def guard(path):
    g=data(path)
    assert g['exit_code']==0 and g['guard_stop'] is None,path
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2},path
    assert g['minimum_system_available_bytes']>=2*1024**3,path
    return g
for item in inv['modules']:
    mod=item['module'];src=read('work/'+mod+'.lean');sha=hashlib.sha256(src).hexdigest()
    assert sha==item['source_sha256']
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',src,re.M)
    f=data('work/formal/'+mod+'/report.json');c=f['check']
    assert f['passed'] and f['source_sha256']==sha and f['kit_commit']==pin
    assert f['checker_unchanged'] and f['checker_sha256']==checker and not f['full_problem_solved']
    assert c['verdict']=='pass' and c['replay']=={'constants':item['declarations'],'ok':True}
    assert not c['newAxioms'] and all(x['ok'] and x['typeMatches'] for x in c['headlines'])
    g=guard('work/evidence/replay-'+mod+'.guard.json')
    assert g['elapsed_seconds']<60 and g['peak_owned_rss_bytes']<4*1024**3
    if mod in new:
        assert item['new_module'] and item['declarations']==new[mod]
        assert sha.encode() in read('REPORT.md')
root=data('work/reference-build-report.json');assert root['passed'] and len(root['stages'])==4
assert all(x['exit_code']==0 for x in root['stages'])
ref=data('work/reference-formal/Rule30Equivalents.P2Scales/report.json')
assert ref['passed'] and ref['check']['replay']=={'constants':117,'ok':True} and not ref['check']['newAxioms']
cache=data('work/bootstrap-completion-report.json')
assert cache['cache_copy_completed_and_independently_verified'] and not cache['hardlinks_used']
assert not cache['old_project_mutated'] and cache['cache_copies_byte_verified']==24246
failed=data('work/evidence/bootstrap_reference.guard.json');assert failed['exit_code']!=0
for label in ['verify_cache_completion','build_reference_roots','check_new_reference_module',
              'final_pin_audit','clock_search_control','wl_clock_search']:
    guard('work/evidence/'+label+'.guard.json')
o=data('work/clock-search-control.json')
assert o['passed'] and o['admissible_periodic_driver_cases']==1302 and o['phase_and_horizon_comparisons']==23940
assert o['missing_zero_control'] and o['missing_anti_control'] and o['missing_mask_period_control']
wl=data('work/wolfram-clock-search.json')
assert wl['passed'] and wl['initial_rows']==1022 and wl['anti_clock_cases_with_mask_zero']==916
assert wl['phase_prediction_comparisons']==25440 and wl['decoded_from_head_differences']
assert not wl['Wolfram_backend_verification'] and not wl['full_problem_solved']
e='work/experiments/'
for label in ['temporal_dfa_probe','audit_temporal_dfa','tree_reader_probe','zip_reader_probe',
              'inspect_learned_readers','mode_descent_probe']:guard(e+'evidence/'+label+'.guard.json')
dfa=data(e+'temporal-dfa-audit.json')
assert dfa['passed'] and dfa['transition_tables_independently_checked']==66282 and dfa['finite_profiles']==44
assert not dfa['Lean_verified'] and not dfa['full_observer_refuted']
for n in ['tree-reader-probe.json','zip-reader-probe.json']:
    o=data(e+n);assert o['candidate'] is None and o['finite_clocks_only'] and not o['Lean_verified']
    assert any(x['status']=='unknown' for x in o['reports'])
inspection=data(e+'learned-reader-inspection.json')
assert inspection['passed'] and not inspection['candidate_uniform_decoder_found']
assert [x['wrong_predictions'] for x in inspection['readers']]==[794,990]
assert all(len(x['mixed_target_state_witnesses'])==x['states'] for x in inspection['readers'])
mode=data(e+'mode-descent-probe.json');last=mode['reports'][-1]
assert last['clock']==64 and last['canonical_plateau_rows']==167168
assert last['unique_derived_observations']==last['unique_modes']==41792 and last['full_mode_collisions']==0
assert all(x['full_mode_collisions']==0 and not x['derived_observer_collisions'] for x in mode['reports'])
first=next(x for x in mode['reports'] if x['clock']==16)
assert first['first_erosion_failure']['initial_parent']==[1]+[0]*8 and first['quadratic_erosion_failures']>0
assert mode['literal_audits']==81 and mode['same_clock_nonmembership_is_not_general_nonrealizability']
assert not mode['Lean_verified'] and not mode['original_OR_observer_refuted']
s=data('summary.json');assert s['new_declarations']==97 and s['fresh_declarations']==1068
assert not s['mode_observer_uniformly_proved'] and not s['parent_bit_observer_proved'] and not s['fixed_center_bridge_proved']
assert not s['full_problem_solved'] and not s['new_prize_submission'] and not s['new_pull_request']
assert s['all_ancestors_P_periodic_in_mode_experiment']
count=archives=0
for old in r.parent.glob('*/artifacts.json'):
    if old.parent.name in {'20261024-seven','20261025-round2','20261025-round2-review',r.name}:continue
    files=json.loads(old.read_bytes())['files']
    for n,h in files.items():assert hashlib.sha256((old.parent/n).read_bytes()).hexdigest()==h,(old.parent.name,n)
    count+=len(files);archives+=1
assert count==2635 and archives==34
for n in m:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(m),'fresh_modules':41,
 'fresh_declarations':1068,'new_declarations':97,'prior_hashes_unchanged':count,
 'mode_observer_proved':False,'full_problem_solved':False}))
