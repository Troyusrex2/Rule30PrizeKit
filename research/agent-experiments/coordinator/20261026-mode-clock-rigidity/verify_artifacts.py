from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
r=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=r,text=True).strip())
prefix=r.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (r/n).read_bytes()
def data(n):return json.loads(read(n))
m=data('artifacts.json')['files']
for n,h in m.items():assert hashlib.sha256(read(n)).hexdigest()==h,n
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256(subprocess.check_output(['git','show',pin+':Check.lean'],cwd=repo)).hexdigest()==checker
mod='Rule30ModeClockRigidityResearch';src=read('work/'+mod+'.lean');sha=hashlib.sha256(src).hexdigest()
assert sha=='f4f31ad9d570647566cf5036ce7ab34db7197e873a99706cdb4734da4df2cc65'
assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',src,re.M)
f=data('work/formal/'+mod+'/report.json');c=f['check']
assert f['passed'] and f['source_sha256']==sha and f['kit_commit']==pin
assert f['checker_unchanged'] and f['checker_sha256']==checker and not f['full_problem_solved']
assert c['verdict']=='pass' and c['replay']=={'constants':10,'ok':True} and not c['newAxioms']
assert len(c['headlines'])==2 and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
old=r.parent/'20261026-even-clock-rigidity/work'
for dep in ['Rule30CommonPastResearch','Rule30OrClockObserverResearch','Rule30ClockJetResearch','Rule30ClockModeResearch']:
    src=read('work/'+dep+'.lean');assert src==(old/(dep+'.lean')).read_bytes()
    report=json.loads((old/'formal'/dep/'report.json').read_bytes())
    assert report['source_sha256']==hashlib.sha256(src).hexdigest() and report['kit_commit']==pin
    assert report['passed'] and report['check']['replay']['ok'] and not report['check']['newAxioms']
for label in ['replay-'+mod,'mode_local_inverse','mode_genuine_local_inverse','audit_genuine_local_collision',
              'mode_unrestricted_mask_probe','mode_clock_controls','equal_profile_strip','plateau_chain_probe']:
    g=data('work/evidence/'+label+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None,label
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert g['minimum_system_available_bytes']>=2*1024**3
    if label=='replay-'+mod:assert g['elapsed_seconds']<60 and g['peak_owned_rss_bytes']<4*1024**3
controls=data('work/mode-clock-controls.json');assert controls['passed']
assert controls['finite_local_rows_without_mask_period']==196 and len(controls['negative_controls'])==3
probe=data('work/mode-unrestricted-mask-probe.json');assert probe['older_mask_period_premise_not_used']
assert all(x['counterexample'] is None for x in probe['reports'])
a=data('work/genuine-local-collision-audit.json')
assert a['passed'] and a['clock']==16 and a['driver_half_clock']==8 and a['period']==32
assert a['shift_for_target_bit_collision']==2 and a['oldest_two_cells_arbitrary']
assert not a['finite_white_ancestry_established'] and not a['uniform_actual_observer_refuted'] and not a['Lean_verified']
assert a['source_sha256']==hashlib.sha256(read('work/mode-genuine-local-inverse.json')).hexdigest()
x,y=a['rotated_witnesses'];assert x['q'][0]!=y['q'][0] and x['S']==y['S']
s=data('summary.json');assert s['new_replayed_constants']==10 and s['headlines']==2
assert s['mask_period_premise_removed'] and s['uniform_mode_clock_rigidity_proved']
for n in ['uniform_mode_inverse_proved','finite_white_counterexample_established','parent_bit_observer_proved',
          'physical_center_bridge_proved','full_problem_solved','new_pull_request','new_prize_submission',
          'Wolfram_backend_verified']:assert not s[n],n
count=archives=0
for old in r.parent.glob('*/artifacts.json'):
    if old.parent.name in {'20261024-seven','20261025-round2','20261025-round2-review',r.name}:continue
    files=json.loads(old.read_bytes())['files']
    for n,h in files.items():assert hashlib.sha256((old.parent/n).read_bytes()).hexdigest()==h,(old.parent.name,n)
    count+=len(files);archives+=1
assert (count,archives)==(3031,36)
for n in m:assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(m),
                 'new_replayed_constants':10,'prior_hashes_unchanged':count,'full_problem_solved':False}))
