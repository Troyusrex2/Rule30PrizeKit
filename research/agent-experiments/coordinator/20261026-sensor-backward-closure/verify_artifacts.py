"""Verify exact working or staged archive bytes, and the scope of its evidence."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip())
prefix=root.relative_to(repo).as_posix()
def read(name):
    if args.staged:return subprocess.check_output(['git','show',':'+prefix+'/'+name],cwd=repo)
    return (root/name).read_bytes()
def data(name):return json.loads(read(name))
manifest=data('artifacts.json')['files']
for name,expected in manifest.items():
    assert hashlib.sha256(read(name)).hexdigest()==expected,name
report=data('work/sensor-kernel-check.json')
source=read('work/Rule30SensorClosureResearch.lean')
assert hashlib.sha256(source).hexdigest()==report['source_sha256']=='8e26936951616c0d40246fcc397a91eddddc2dc98928b10d9820d7a4e90bc0b8'
assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native',source,re.M)
assert report['passed'] and report['checker_unchanged'] and not report['full_problem_solved']
assert report['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
checked=report['check']
assert checked['verdict']=='pass' and checked['replay']=={'constants':134,'ok':True} and not checked['newAxioms']
assert len(checked['headlines'])==3 and all(h['ok'] and h['typeMatches'] for h in checked['headlines'])
guard=data('work/evidence/check_sensor.guard.json')
assert guard['exit_code']==0 and guard['guard_stop'] is None
assert guard['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
control=data('work/independent-sensor-check.json')
assert control['pass'] and control['corruptions_rejected']==2 and control['H']==6
assert not control['all_time_counterexample']
beyond=data('work/beyond-window.json')
assert beyond['first_nonzero_center']==7 and beyond['first_W_failure']=={'t':9,'p':246}
assert not beyond['all_time_W'] and not beyond['all_time_invisible']
summary=data('summary.json')
assert not summary['full_problem_solved'] and not summary['new_prize_submission']
for name in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(name),re.I),name
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(manifest),
                  'replayed_declarations':134,'headlines':3,'full_problem_solved':False}))
