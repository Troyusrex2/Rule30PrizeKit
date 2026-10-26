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
source=read('work/Rule30CommonPastResearch.lean')
sha='17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3'
assert hashlib.sha256(source).hexdigest()==sha
assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native',source,re.M)
r=data('work/formal/Rule30CommonPastResearch/report.json')
assert r['passed'] and r['source_sha256']==sha and r['checker_unchanged'] and not r['full_problem_solved']
assert r['kit_commit']=='0090056412733accaa27643d3cbbf982104f2251'
assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
c=r['check'];assert c['verdict']=='pass' and not c['newAxioms'] and c['replay']=={'constants':100,'ok':True}
assert len(c['headlines'])==7 and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
g=data('work/kernel.guard.json')
assert g['exit_code']==0 and g['guard_stop'] is None
assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
audit=data('work/independent-audit.json')
assert audit['passed'] and audit['all_prefix_triples_checked']==4680 and audit['literal_physical_cells_checked']==38880
assert audit['finite_image_membership_controls']==512 and not audit['Lean_verified']
cs=data('work/common-subset-probe-8.json')
assert cs['nontrivial_modes_tested']==774400 and cs['common_survivors']==6792
assert not cs['subset_failure_survivors'] and not cs['unbounded_subset_preservation_proved']
cycle=data('work/cycle-subset.json')['records']
assert [(x['period'],x['status']) for x in cycle]==[(2,'unsat'),(4,'unsat'),(8,'unsat'),(16,'unsat'),(32,'unknown')]
s=data('summary.json')
assert s['all_future_common_past_lift'] and s['finite_past_requires_stated_all_time_subset']
assert not s['initial_only_subset_upgrade_proved'] and not s['fixed_center_past_extension_proved']
assert not s['full_problem_solved'] and not s['new_prize_submission'] and s['prior_hashes_unchanged']==1583
for n in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(manifest),'replayed_declarations':100,'headlines':7,'full_problem_solved':False}))
