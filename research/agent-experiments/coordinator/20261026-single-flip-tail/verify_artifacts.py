from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip())
prefix=root.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if a.staged else (root/n).read_bytes()
def data(n):return json.loads(read(n))
m=data('artifacts.json')['files']
for n,h in m.items():assert hashlib.sha256(read(n)).hexdigest()==h,n
for module,count,heads,sha in [
 ('Rule30SingleFlipTailResearch',63,14,'1dd4a7baa94c55f010252e55a2a6e4adb397ff81414dc70914ff997219b48f39'),
 ('Rule30SharedTailCounterResearch',58,9,'0f90ba4301fc73a982815afab6ea8d3b5442511e722465eac71b921d4cce3e9f'),
 ('Rule30SharedTailDelayResearch',23,5,'9121a94253e3fdfe9773ae2a0f5ad7190c012bcd76ec459c314d8b9e6e85e321')]:
    source=read('work/'+module+'.lean');assert hashlib.sha256(source).hexdigest()==sha
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native',source,re.M)
    r=data('work/formal/'+module+'/report.json');c=r['check']
    assert r['passed'] and r['source_sha256']==sha and r['checker_unchanged'] and not r['full_problem_solved']
    assert r['kit_commit']=='0090056412733accaa27643d3cbbf982104f2251'
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and not c['newAxioms'] and c['replay']=={'constants':count,'ok':True}
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    g=data('work/remote-evidence/check_formal-'+module+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
audit=data('work/independent-audit.json')
assert audit['passed'] and audit['literal_causal_cells_checked']==41280 and audit['corrupt_tail_rejected']
assert audit['single_flip_position']==7 and audit['known_precursor_spatial_shift']==2
assert audit['strip_edges_checked']==1872 and audit['independently_recomputed_periodic_core_states']==64
assert len(audit['finite_samples'])==12 and all(s['status']=='different' and s['reader_state']==15 and s['first_difference']>s['delay'] for s in audit['finite_samples'])
assert audit['finite_samples'][-1]['width']==2064 and audit['finite_samples'][-1]['first_difference']==1377
assert not audit['Lean_verified'] and not audit['unbounded_eventual_separation_proved']
wl=data('work/wolfram-control.json');assert wl['passed'] and wl['scalar_cells_checked']==4160
assert wl['built_in_cellular_automaton']==30 and wl['causal_cone_stays_inside_initial_array'] and not wl['Lean_verified']
assert data('work/evidence/wolfram-cli.log')==wl
orbit=data('work/orbit-sections.json');assert orbit['controls']==8239 and not orbit['closed']
assert orbit['processed']==18 and orbit['discovered']==34 and orbit['stop']['status']=='section_state_cap'
assert orbit['stop']['discovered']==12002 and not orbit['infinite_signalizer_proved']
for name in ['orbit_sections','strip_observer','inspect_strip','nonalternating_resync','extract_single','independent_audit','wl_control']:
    g=data('work/evidence/'+name+'.guard.json');assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
s=data('summary.json');assert s['single_flip_infinite_tail_invisibility_proved'] and s['arbitrary_finite_single_flip_delay_proved']
assert s['nonconstant_OR_common_tail_reconstruction_false'] and not s['finite_individual_background_counterexample']
assert not s['full_problem_solved'] and not s['reader_completeness_proved'] and not s['new_prize_submission']
assert s['local_wolfram_control_passed'] and not s['Wolfram_backend_verified'] and s['prior_hashes_unchanged']==1881
for n in m:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(m),'new_declarations':63,
 'dependency_declarations':[58,23],'local_wolfram_control_passed':True,'full_problem_solved':False}))
