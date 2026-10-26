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
source=read('work/Rule30IsolatedDefectResearch.lean')
sha='bb98722222ef8576c7c76994f7713da45bf5dfe99623fe6d294aa55ad090eff9'
assert hashlib.sha256(source).hexdigest()==sha
assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native',source,re.M)
r=data('work/formal/Rule30IsolatedDefectResearch/report.json')
assert r['passed'] and r['source_sha256']==sha and r['checker_unchanged'] and not r['full_problem_solved']
assert r['kit_commit']=='0090056412733accaa27643d3cbbf982104f2251'
assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
c=r['check'];assert c['verdict']=='pass' and not c['newAxioms'] and c['replay']=={'constants':52,'ok':True}
assert len(c['headlines'])==3 and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
g=data('work/kernel.guard.json')
assert g['exit_code']==0 and g['guard_stop'] is None
assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
audit=data('work/independent-tree-audit.json')
assert audit['passed'] and audit['nodes']==9 and len(audit['corruptions_rejected'])==2 and not audit['Lean_verified']
tree=data('work/word-tree-odd.json');assert tree['unsat'] and tree['nodes']==9 and not tree['Lean_verified']
s=data('summary.json');assert not s['full_problem_solved'] and not s['new_prize_submission'] and s['prior_hashes_unchanged']==1548
for n in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(manifest),'replayed_declarations':52,'full_problem_solved':False}))
