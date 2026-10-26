from pathlib import Path
from fractions import Fraction
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip())
prefix=root.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if a.staged else (root/n).read_bytes()
def data(n):return json.loads(read(n))
manifest=data('artifacts.json')['files']
for n,h in manifest.items():assert hashlib.sha256(read(n)).hexdigest()==h,n
for K,m in [(2,1),(3,0),(3,1)]:
    c=data(f'work/farkas-exact-{K}-{m}.json');s=data('work/'+c['system_file'])
    sums=[Fraction(0) for _ in range(s['variables'])];margin=Fraction(0)
    for i,v in c['weights']:
        v=Fraction(v);assert v>=0
        margin+=v*s['rhs'][i]
        for j,k in s['rows'][i].items():sums[int(j)]+=v*k
    assert not any(sums) and margin==Fraction(c['rhs_margin']) and margin>0
audit=data('work/independent-audit.json')
assert audit['passed'] and not audit['Lean_verified'] and len(audit['reports'])==3
assert all(r['passed'] and r['changed_weight_rejected'] and r['negative_weight_rejected'] for r in audit['reports'])
rank=data('work/context-rank-complete.json');assert [r['status'] for r in rank['reports']]==['unsat']*3+['unknown_wall_cap']*5
rays=data('work/rationalized-rays.json');assert all(r['status']=='exact_farkas' and r['nullity']==1 for r in rays['reports'])
for n in ['rank_cases','graph_lp','rationalize_ray','independent_audit']:
    g=data('work/evidence/'+n+'.guard.json');assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
s=data('summary.json');assert s['exact_farkas_certificates']==3 and not s['Lean_verified']
assert not s['full_problem_solved'] and not s['sink_separation_proved'] and not s['new_prize_submission']
assert s['prior_hashes_unchanged']==1779 and s['four_context_cases']=='unknown'
for n in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(manifest),
 'exact_rational_certificates':3,'Lean_verified':False,'full_problem_solved':False}))
