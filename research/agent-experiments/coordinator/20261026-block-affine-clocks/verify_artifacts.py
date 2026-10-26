from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');a=p.parse_args()
r=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=r,text=True).strip());prefix=r.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if a.staged else (r/n).read_bytes()
def data(n):return json.loads(read(n))
m=data('artifacts.json')['files']
for n,h in m.items():assert hashlib.sha256(read(n)).hexdigest()==h,n
def guard(n):
    g=data(n);assert g['exit_code']==0 and g['guard_stop'] is None,n
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2},n
for mod,count,heads,sha in [('Rule30BlockClockResearch',112,8,'180b34d077c5bf36296cddc8d0666e340f9ef1514ca803fa10dbd4305596c9d3'),
 ('Rule30CommonPastResearch',100,7,'17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3')]:
    src=read('work/'+mod+'.lean');assert hashlib.sha256(src).hexdigest()==sha
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native',src,re.M)
    f=data('work/formal/'+mod+'/report.json');c=f['check']
    assert f['passed'] and f['source_sha256']==sha and f['checker_unchanged'] and not f['full_problem_solved']
    assert f['kit_commit']=='0090056412733accaa27643d3cbbf982104f2251'
    assert f['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True} and not c['newAxioms']
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    guard('work/remote-evidence/replay-'+mod+'.guard.json')
c=data('work/independent-control.json')
assert c['passed'] and c['affine_composition_cases']==32768 and c['quartic_cases']==512
assert c['two_gate_cases']==128 and c['literal_two_step_patterns']==32 and c['odd_period_negative_control_return_after_four']==4
assert c['packed_row_updates']==2976602 and c['literal_truth_table_cells']==4674
assert len(c['period_controls'])==13 and all(x['passed'] for x in c['period_controls'])
w=data('work/wolfram-control.json');assert w['passed'] and w['initial_rows']==510 and w['period_cell_comparisons']==88132
assert w['built_in_cellular_automaton']==30 and not w['Wolfram_backend_verification']
for name in ['independent_control','wl_control','audit_profiles']:guard('work/evidence/'+name+'.guard.json')
g=data('work/profile-audit.json');assert g['passed'] and g['finite_clocks_only'] and not g['Lean_verified']
assert g['reports'][-1]['states']==171780 and g['reports'][-1]['edges']==171784
assert g['reports'][-1]['maximum_shortest_word_length']==106 and all(x['noncore_merges']==0 for x in g['reports'])
for name in ['period_front_probe','global_no00']:guard('work/diagnostics/evidence/'+name+'.guard.json')
s='work/searches/'
for filename in ['nfa-result.json','reverse-nfa-result.json','hinted-reverse-nfa-result.json']:
    o=data(s+filename);assert o['candidate'] is None and not o['candidate_verified_by_python']
    assert not o['Lean_verified'] and not o['full_problem_solved']
    assert all((h['positive'],h['negative'],h['implications'])==(337,350,2741) for h in o['history'])
for name in ['learn_nfa','learn_reverse_nfa','learn_hinted_reverse_nfa','context_lex_rank','prefix_lex_rank','audit_nfa']:
    guard(s+'evidence/'+name+'.guard.json')
na=data(s+'nfa-audit.json');assert na['passed'] and na['reverse_carry_controls']==17472
assert na['forced_known_model_encoding_passed'] and not na['actual_search_constraints_removed']
assert len(na['sample_audits'])==3 and all(x['passed'] for x in na['sample_audits'])
for filename,unsat,unknown in [('context-lex-rank.json',16,2),('prefix-lex-rank.json',5,3)]:
    o=data(s+filename);assert o['candidate'] is None
    assert sum(x['status']=='unsat' for x in o['reports'])==unsat
    assert sum(x['status']=='unknown' for x in o['reports'])==unknown
ext=data('work/related-source-audit.json');assert len(ext)==4
assert all(not x['adopted'] and not x['full_kernel_replayed_here'] for x in ext)
summary=data('summary.json');assert summary['sharper_clock_formalized'] and summary['block_return_proved']
assert not summary['mathematical_novelty_claim'] and summary['prior_hashes_unchanged']==2055
assert not summary['sink_separation_proved'] and not summary['unconditional_preservation_proved']
assert not summary['full_problem_solved'] and not summary['new_prize_submission']
for n in m:assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(m),'new_declarations':112,
                  'full_problem_solved':False,'mathematical_novelty_claim':False}))
