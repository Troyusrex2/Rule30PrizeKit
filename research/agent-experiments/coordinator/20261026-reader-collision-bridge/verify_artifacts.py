from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip())
prefix=root.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (root/n).read_bytes()
def data(n):return json.loads(read(n))
manifest=data('artifacts.json')['files']
for n,h in manifest.items():assert hashlib.sha256(read(n)).hexdigest()==h,n
modules=[('Rule30ReaderCollisionBridgeResearch',47,7,'09bbb9147e87b58b74e7b7816a8ee319a99135c52728ef0f1ea67bedd8735f6b'),
 ('Rule30CommonPastResearch',100,7,'17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3'),
 ('Rule30FrontReductionResearch',81,6,'c6e009b69c20c73aa4eff738be4e7fc04a5ffe280793e9af0af2a8877a304a3f'),
 ('Rule30ColumnReaderResearch',119,3,'ad1d09b6d460b1849017fcf7c99151ad0304ceee8dfc80e78f43bfc1a917da3b'),
 ('Rule30ReaderSeparationResearch',18,6,'b47e4ee93484c4dc33b966b313411f20ebc93e4ae965ada6b499e54183006fe0')]
def guard(n):
    g=data(n);assert g['exit_code']==0 and g['guard_stop'] is None,n
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2},n
for mod,count,heads,sha in modules:
    source=read('work/'+mod+'.lean');assert hashlib.sha256(source).hexdigest()==sha
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native',source,re.M)
    f=data('work/formal/'+mod+'/report.json');c=f['check']
    assert f['passed'] and f['source_sha256']==sha and f['checker_unchanged'] and not f['full_problem_solved']
    assert f['kit_commit']=='0090056412733accaa27643d3cbbf982104f2251'
    assert f['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and not c['newAxioms'] and c['replay']=={'constants':count,'ok':True}
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    guard('work/remote-evidence/replay-'+mod+'.guard.json')
a=data('work/independent-audit.json')
assert a['passed'] and a['literal_cells_checked']==3029216 and a['accepted_pairs']==1832
assert a['state16_pairs']==448 and a['permanent_extension_checks']==2768
assert a['state16_cannot_be_treated_as_permanent']['first_lost_difference']==1
assert not a['sink_separation_proved'] and not a['Lean_verified']
w=data('work/wolfram-control.json');assert w['passed'] and len(w['cases'])==5 and w['scalar_cells_available']==910
assert w['built_in_cellular_automaton']==30 and not w['Wolfram_backend_verification']
for name in ['independent_audit','wl_control']:guard('work/evidence/'+name+'.guard.json')
s='work/invariant-search/'
for name,script in [('ice-invariant','ice_invariant'),('ice-safe','ice_safe'),('ice-tree','ice_tree'),
 ('ice-dyadic','ice_dyadic'),('ice-sym-dyadic','ice_dyadic_sym'),('ice-typed','ice_typed')]:
    out=data(s+name+'.json');assert not out['candidate_verified_by_python'] and out['candidate'] is None
    assert not out['full_problem_solved'] and out['stop_reason']
    guard(s+'evidence/'+script+'.guard.json')
pa=data(s+'protocol-audit.json');assert pa['passed'] and len(pa['sample_audits'])==6
assert pa['cyclic_extension_edges_checked']==7184 and pa['noncyclic_carries_rejected']==17328
assert all(x['all_semantic_checks_passed'] for x in pa['sample_audits'])
ba=data(s+'backward-audit.json');assert ba['passed'] and ba['literal_unrolling_cases']==31056
back=data(s+'exact-backward.json');assert not back['all_word_fixed_point'] and back['stop_reason']=='composition_state_cap'
assert [x['minimal_states'] for x in back['history']]==[7,129,12306]
assert all(x['all_seed_lengths_passed'] and not x['same_language'] for x in back['history'])
for name in ['audit_protocol','exact_backward','audit_backward']:guard(s+'evidence/'+name+'.guard.json')
summary=data('summary.json');assert summary['accepted_collision_clock_proved'] and summary['sink_separation_implies_preservation_proved']
assert summary['prior_hashes_unchanged']==1941 and not summary['sink_separation_proved']
assert not summary['full_problem_solved'] and not summary['new_prize_submission']
for n in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(manifest),
                  'new_declarations':47,'dependency_declarations':[100,81,119,18],
                  'full_problem_solved':False}))
