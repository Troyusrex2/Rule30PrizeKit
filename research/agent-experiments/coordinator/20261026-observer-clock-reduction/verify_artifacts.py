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
mods=[('Rule30CommonPastResearch',100,7,'17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3'),
 ('Rule30ColumnReaderResearch',119,3,'ad1d09b6d460b1849017fcf7c99151ad0304ceee8dfc80e78f43bfc1a917da3b'),
 ('Rule30ReaderEquivalenceResearch',83,5,'574920fd28265f590b6f030784bb22979770f0fb1da023f328825bc3cade6dd7'),
 ('Rule30ReaderCanonicalResearch',215,7,'832fd7632331f8ad6101bc4725a7b954e81e692843017c7df529a52a3901641a'),
 ('Rule30OrClockObserverResearch',24,6,'9928288f7c038406e6979852d845f6de17a5d8f887bddefe3d31494e2b8b83c2'),
 ('Rule30ReaderObserverReductionResearch',129,4,'ed0266339602889151012650bc5b0fe0a53c46d7d706c29a44544f5e7b41f805')]
for mod,count,heads,sha in mods:
    src=read('work/'+mod+'.lean');assert hashlib.sha256(src).hexdigest()==sha
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',src,re.M)
    f=data('work/formal/'+mod+'/report.json');c=f['check']
    assert f['passed'] and f['source_sha256']==sha and f['checker_unchanged'] and not f['full_problem_solved']
    assert f['kit_commit']=='0090056412733accaa27643d3cbbf982104f2251'
    assert f['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True} and not c['newAxioms']
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    path='work/evidence/replay-'+mod+'.guard.json';guard(path)
    assert data(path)['peak_owned_rss_bytes']<4*1024**3
    assert sha.encode() in read('REPORT.md')
for label in ['plateau_probe','independent_control','wl_control','extension_audit']:
    guard('work/evidence/'+label+'.guard.json')
o=data('work/independent-control.json')
assert o['passed'] and o['periodic_driver_cases']==508 and o['zero_assumption_negative_control_passed']
assert o['plateau_literal_truth_table_passed'] and o['plateau_has_no_white_ancestry_certificate']
assert [x['clock'] for x in o['all_clocks_tested']]==list(range(1,8))
assert sum(x['all_admissible_pairs'] for x in o['all_clocks_tested'])==6558
o=data('work/extension-audit.json');assert o['passed'] and len(o['states'])==250 and o['counterexample'] is None
o=data('work/plateau-probe.json')
assert not o['white_boundary_imposed'] and not o['canonical_observer_refuted']
assert len(o['reports'])==6 and sum(x['status']=='sat' for x in o['reports'])==2
w=data('work/wolfram-control.json')
assert w['passed'] and w['initial_rows']==510 and w['profile_pairs']==2568
assert w['antiperiodic_cases']==404 and w['antiperiodic_with_mask_zero']==404 and w['mask_recovery_comparisons']==2924
assert w['built_in_cellular_automaton']==30 and not w['Wolfram_backend_verification']
diag='work/diagnostics/'
for name in ['mealy_probe','linear_decoder_probe','audit_linear_decoder','audit_penultimate_linear',
             'nonlinear_decoder_probe','nonlinear_decoder_fast','extract_newton_decoder']:
    guard(diag+'evidence/'+name+'.guard.json')
o=data(diag+'mealy-probe.json')
assert o['passed'] and o['complete_fixed_point'] and o['closed_automaton_states']==9841
assert o['global_action_classes_within_bound']==9841 and o['relations']==[] and o['literal_and_section_controls']==15246
old=data(diag+'nonlinear-decoder-probe.json');fast=data(diag+'nonlinear-decoder-fast.json')
assert [x['width'] for x in old['reports']]==list(range(3,14))
assert [x['width'] for x in fast['reports']]==list(range(3,15))
assert all(x['complete_layers'] and x['complete_code_recovered'] for x in old['reports'])
assert all(x['cubic_code_recovery'] and x['cubic_raw_recovery'] for x in fast['reports'])
assert [x['rank'] for x in fast['reports'][-1]['layers']]==[130,3106,7073]
for oo in old['reports']:
    ff=next(x for x in fast['reports'] if x['width']==oo['width'])
    for layer in oo['layers']:
        fl=next(x for x in ff['layers'] if x['degree']==layer['degree'])
        assert fl['rank']==layer['rank'] and fl['recovered_coordinates']==layer['recovered_coordinates']
o=data(diag+'newton-decoder-filters.json')
assert o['passed'] and o['finite_widths_only'] and not o['uniform_decoder_proved']
assert [x['width'] for x in o['reports']]==list(range(4,11))
assert [x['term_count'] for x in o['reports']]==[1,4,7,19,30,63,132]
assert sum(x['literal_cells_checked'] for x in o['reports'])==443648
assert sum(x['all_canonical_rows_checked'] for x in o['reports'])==1016
for x in o['reports']:assert x['degree']<=3 and max(map(len,x['terms']))<=3
for name,coord in [('linear-decoder-negative-control.json',1),('penultimate-linear-negative-control.json',2)]:
    o=data(diag+name);assert o['passed'] and o['target_code_coordinate']==coord
    assert len(o['witness'])%2==0 and o['xor_of_targets']==1
    assert all(sum(v['head_period'][t] for v in o['witness'])%2==0 for t in range(o['whole_period']))
    assert sum(v['target'] for v in o['witness'])%2==1
    if coord==2:assert all(v['target']==v['canonical_word'][-2] for v in o['witness'])
summary=data('summary.json')
assert summary['parent_bit_reduction_proved'] and summary['anti_clock_or_inverse_proved']
assert summary['local_plateau_weakening_refuted'] and summary['prior_hashes_unchanged']==2233
assert not summary['parent_bit_observer_proved'] and not summary['full_problem_solved'] and not summary['new_prize_submission']
for n in m:assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(m),'new_module_declarations':153,
                  'parent_bit_observer_proved':False,'full_problem_solved':False}))
