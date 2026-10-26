from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip())
prefix=root.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if a.staged else (root/n).read_bytes()
def data(n):return json.loads(read(n))
manifest=data('artifacts.json')['files']
for n,h in manifest.items():assert hashlib.sha256(read(n)).hexdigest()==h,n
for module,count,heads,sha,guard in [
 ('Rule30SharedTailCounterResearch',58,9,'0f90ba4301fc73a982815afab6ea8d3b5442511e722465eac71b921d4cce3e9f','remote-evidence/check_formal-Rule30SharedTailCounterResearch'),
 ('Rule30SharedTailDelayResearch',23,5,'9121a94253e3fdfe9773ae2a0f5ad7190c012bcd76ec459c314d8b9e6e85e321','remote-evidence/check_formal-Rule30SharedTailDelayResearch'),
 ('Rule30SinkDelayResearch',15,2,'0d093d5878f183cb0a0440d9c2290a2792e48fd8a7ee8bc119c231bdbf8a8258','remote-evidence/check_formal-Rule30SinkDelayResearch'),
 ('Rule30ColumnReaderResearch',119,3,'ad1d09b6d460b1849017fcf7c99151ad0304ceee8dfc80e78f43bfc1a917da3b','reader-dependency'),
 ('Rule30CommonPastResearch',100,7,'17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3','common-dependency')]:
    source=read('work/'+module+'.lean');assert hashlib.sha256(source).hexdigest()==sha
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native',source,re.M)
    r=data('work/formal/'+module+'/report.json');c=r['check']
    assert r['passed'] and r['source_sha256']==sha and r['checker_unchanged'] and not r['full_problem_solved']
    assert r['kit_commit']=='0090056412733accaa27643d3cbbf982104f2251'
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and not c['newAxioms'] and c['replay']=={'constants':count,'ok':True}
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    g=data('work/'+guard+'.guard.json');assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
audit=data('work/independent-audit.json')
assert audit['passed'] and audit['literal_causal_cells_checked']==41280 and audit['corrupt_tail_rejected']
assert audit['initial_difference_depths']==[1,2,3,4] and audit['known_loss_precursor_matched_after_time_shift']==6
assert not audit['Lean_verified'] and not audit['reader_completeness_proved']
tail=data('work/explicit-tail.json');assert tail['a_prefix']==[170,93,162,83,178]
assert tail['b_prefix']==[170,170,117,138,77] and tail['shared_tail']==[202,43,172,178]
assert tail['not_a_right_bounded_example'] and not tail['Lean_verified']
samples=data('work/delay-samples.json');assert len(samples['reports'])==13 and samples['literal_scalar_controls']==1916
assert all(r['reader_state']==15 and r['finite_prefix_width']==2*r['requested_delay']+8 and r['status']=='different' and r['first_observed_difference']>r['requested_delay'] for r in samples['reports'])
assert samples['reports'][-1]['first_observed_difference']==1373 and not samples['unbounded_eventual_separation_proved']
for name in ['golden_difference','split_probe','extract_tail','independent_audit','delay_samples']:
    g=data('work/evidence/'+name+'.guard.json');assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
s=data('summary.json');assert s['shared_infinite_tail_counterexample_proved'] and s['arbitrary_finite_sink_delay_proved']
assert s['defect_only_uniform_bound_refuted'] and s['fixed_initial_difference_depths']==[1,2,3,4]
assert not s['reader_completeness_proved'] and not s['sink_separation_proved'] and not s['full_problem_solved']
assert not s['new_prize_submission'] and s['prior_hashes_unchanged']==1818
for n in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(manifest),'new_declarations':[58,23,15],
 'dependency_declarations':[119,100],'arbitrary_finite_sink_delay_proved':True,'full_problem_solved':False}))
