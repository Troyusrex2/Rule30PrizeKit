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
 ('Rule30ColumnReaderResearch',119,3,'ad1d09b6d460b1849017fcf7c99151ad0304ceee8dfc80e78f43bfc1a917da3b','kernel'),
 ('Rule30CommonPastResearch',100,7,'17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3','dependency')]:
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
assert audit['passed'] and audit['scalar_membership_tests']==5461 and audit['certificate_states']==47
assert len(audit['corruptions_rejected'])==2 and audit['clock64_is_incomplete']
assert not audit['Lean_verified'] and not audit['reader_completeness_proved']
learner=data('work/learned-reader.json')
assert learner['stop_reason']=='bounded_candidate' and len(learner['dfa']['transitions'])==17
assert learner['membership_queries']==93113 and learner['exact_membership_controls']==1364
eq=learner['iterations'][-1]['equivalence'] if 'iterations' in learner else learner['history'][-1]['equivalence']
assert eq['checked']==93381 and eq['exhaustive_through']==8 and eq['heldout']==6000
assert not learner['regularity_proved']
prod=data('work/invariance-product.json');assert prod['closed'] and len(prod['states'])==47 and not prod['completeness_proved']
clock=data('work/clock-product.json')
assert [(r['temporal_clock'],r['states']) for r in clock['reports']]==[(2,64),(4,144),(8,1296),(16,4624)]
assert all(r['closed'] and r['counterexample'] is None and not r['Lean_verified'] for r in clock['reports'])
for r in clock['reports']:assert hashlib.sha256(read('work/'+r['graph_file'])).hexdigest()==r['graph_sha256']
macro=data('work/macro-rank.json')
assert [r['status'] for r in macro['reports']]==['unsat','unsat','unsat','graph_node_cap']
s=data('summary.json')
assert s['reader_soundness_proved'] and not s['reader_completeness_proved']
assert not s['collision_clock_proved'] and not s['unconditional_subset_preservation_proved']
assert not s['full_problem_solved'] and not s['new_prize_submission'] and s['prior_hashes_unchanged']==1650
for n in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(manifest),'new_module_declarations':119,
                 'dependency_declarations':100,'reader_completeness_proved':False,'full_problem_solved':False}))
