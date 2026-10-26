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
    g=data('work/evidence/'+n+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None,n
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2},n
mods=[('Rule30CommonPastResearch',100,7,'17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3'),
      ('Rule30ColumnReaderResearch',119,3,'ad1d09b6d460b1849017fcf7c99151ad0304ceee8dfc80e78f43bfc1a917da3b'),
      ('Rule30ReaderEquivalenceResearch',83,5,'574920fd28265f590b6f030784bb22979770f0fb1da023f328825bc3cade6dd7'),
      ('Rule30ReaderCanonicalResearch',215,7,'832fd7632331f8ad6101bc4725a7b954e81e692843017c7df529a52a3901641a')]
for mod,count,heads,sha in mods:
    src=read('work/'+mod+'.lean');assert hashlib.sha256(src).hexdigest()==sha
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',src,re.M)
    f=data('work/formal/'+mod+'/report.json');c=f['check']
    assert f['passed'] and f['source_sha256']==sha and f['checker_unchanged'] and not f['full_problem_solved']
    assert f['kit_commit']=='0090056412733accaa27643d3cbbf982104f2251'
    assert f['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True} and not c['newAxioms']
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    guard('replay-'+mod)
    assert sha.encode() in read('REPORT.md')
for label in ['reader_equivalence_audit','orbit_partition','audit_orbits','canonical_audit','canonical_rank','audit_canonical','wl_control','orbit_partition_large']:
    guard(label)
eq=data('work/reader-equivalence-audit.json')
assert [eq[k]['reachable_states'] for k in ['reflexive','symmetric','transitive']]==[3,17,151]
assert all(eq[k]['passed'] and eq[k]['counterexample'] is None for k in ['reflexive','symmetric','transitive'])
can=data('work/canonical-audit.json')
for k,n in [('coverage',21),('unique',86),('time_invariance',14)]:
    assert len(can[k]['states'])==n and can[k]['complete'] and can[k]['counterexample'] is None
small=data('work/orbit-partition.json');large=data('work/large-orbit-partition.json')
assert [x['width'] for x in small['reports']]==list(range(1,25))
assert [x['width'] for x in large['reports']]==[8,*range(25,31)]
for result in [small,large]:
    assert result['counterexample'] is None and result['hash_matches_compared_exactly'] and result['finite_widths_only']
    assert not result['Lean_verified'] and not result['reader_completeness_proved']
    for x in result['reports']:
        assert x['complete'] and x['states_checked']==1<<x['width']
        assert x['cycles_with_shorter_head_period']==0
        if x['width']>=3:assert x['distinct_column_profiles']==1<<(x['width']-1)
for key in set(small['reports'][7]) - {'seconds'}:assert small['reports'][7][key]==large['reports'][0][key]
assert large['reports'][-1]['states_checked']==1073741824
o=data('work/orbit-audit.json')
assert o['passed'] and o['literal_cells_checked']==669924 and o['all_pair_comparisons_through_width8']==87380
assert o['minimal_rotation_controls']==8190 and o['exact_comparisons_not_probabilistic_hashes']
o=data('work/canonical-independent-audit.json')
assert o['passed'] and o['word_witness_language_checks']==32767 and o['literal_rule30_cells']==425986
assert o['canonical_pair_checks']==21861
o=data('work/canonical-rank.json')
assert o['candidate'] is None and len(o['reports'])==18 and all(x['status']=='unsat' for x in o['reports'])
assert not o['Lean_verified'] and not o['sink_separation_proved']
w=data('work/wolfram-control.json')
assert w['passed'] and w['initial_rows']==2046 and w['literal_builtin_cells']==18434
assert w['built_in_cellular_automaton']==30 and not w['Wolfram_backend_verification']
summary=data('summary.json')
assert summary['canonical_forms_proved'] and summary['normalization_commutes_proved']
assert summary['observer_equivalence_proved'] and summary['prior_hashes_unchanged']==2143
assert not summary['canonical_observer_proved'] and not summary['full_problem_solved'] and not summary['new_prize_submission']
for n in m:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(m),'new_module_declarations':298,
                  'canonical_observer_proved':False,'full_problem_solved':False}))
