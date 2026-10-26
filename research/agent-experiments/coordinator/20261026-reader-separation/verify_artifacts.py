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
for module,count,heads,sha,label in [
 ('Rule30ReaderSeparationResearch',18,6,'b47e4ee93484c4dc33b966b313411f20ebc93e4ae965ada6b499e54183006fe0','kernel'),
 ('Rule30LateSeparationResearch',12,3,'3f2a9cf2997c35f01816479a59ad5fd17ebe481cd94248bc35f0daf9b41db8ab','late-kernel'),
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
    g=data('work/'+label+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
audit=data('work/independent-audit.json')
assert audit['passed'] and audit['factor_controls']==5461 and audit['wrong_phase_rejected']
assert audit['three_width_bound_falsified']=={'width':22,'first_difference_time':72,'literal_all_73_steps_checked':True}
assert not audit['Lean_verified'] and not audit['sink_separation_proved']
late=data('work/late-separation.json')
assert late['stop_reason']=='witness' and late['witness']['first_difference_time']==72
assert late['witness']['width']==22 and late['witness']['status']=='different'
assert late['reports'][-1]['complete'] is False
assert all(r['complete'] for r in late['reports'][:-1]) and late['reports'][-2]['width']==21
degree=data('work/complexity-probe.json')
assert degree['controls']==65814 and degree['strict_degree_growth_counterexample']['degrees']==[29,31,31]
assert degree['pair_degree_decrease_counterexample']['degrees']==[31,30,28] and degree['period_decrease_counterexample'] is None
rank=data('work/context-rank-complete.json')
assert [r['status'] for r in rank['reports']]==['unsat']*3+['unknown_wall_cap']*5
assert data('work/context-original.guard.json')['guard_stop']=='wall_time'
for n in ['evidence/independent_audit.guard.json','evidence/complexity_probe.guard.json','evidence/rank_cases.guard.json','late.guard.json']:
    g=data('work/'+n);assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
s=data('summary.json')
assert s['reader_complete_outside_sink'] and s['reader_state_period_two'] and s['sink_membership_invariant']
assert s['three_width_observation_bound_false'] and not s['reader_completeness_proved'] and not s['sink_separation_proved']
assert not s['full_problem_solved'] and not s['new_prize_submission'] and s['prior_hashes_unchanged']==1719
for n in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(manifest),'new_declarations':[18,12],
                 'dependency_declarations':[119,100],'reader_completeness_proved':False,'full_problem_solved':False}))
