from pathlib import Path
import argparse,hashlib,io,json,re,subprocess,tarfile

p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
r=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=r,text=True).strip())
prefix=r.relative_to(repo).as_posix()
def read(n):
    return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (r/n).read_bytes()
def data(n):return json.loads(read(n))
m=data('artifacts.json')['files']
for n,h in m.items():assert hashlib.sha256(read(n)).hexdigest()==h,n
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert data('work/environment.json')['kit']['commit']==pin
official=subprocess.check_output(['git','archive','--format=tar',pin],cwd=repo)
with tarfile.open(fileobj=io.BytesIO(official),mode='r:') as t:
    assert hashlib.sha256(t.extractfile('Check.lean').read()).hexdigest()==checker
    manifest=data('work/source-manifest.json');assert manifest['pin']==pin
    for n,h in manifest['files'].items():assert hashlib.sha256(t.extractfile(n).read()).hexdigest()==h,n

def guard(name):
    g=data('work/evidence/'+name+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None,name
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert g['minimum_system_available_bytes']>=2*1024**3
    return g

mods=['Rule30CommonPastResearch','Rule30OrClockObserverResearch','Rule30ClockJetResearch',
      'Rule30ClockModeResearch','Rule30EvenModeRigidityResearch','Rule30CoupledGerms']
for mod in mods:
    src=read('work/'+mod+'.lean');sha=hashlib.sha256(src).hexdigest()
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',src,re.M)
    f=data('work/formal/'+mod+'/report.json');c=f['check']
    assert f['passed'] and f['source_sha256']==sha and f['kit_commit']==pin
    assert f['checker_unchanged'] and f['checker_sha256']==checker
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms']
    assert all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    assert not f['full_problem_solved']
    g=guard('replay_external_germs' if mod=='Rule30CoupledGerms' else 'replay-'+mod)
    if mod in ['Rule30CoupledGerms','Rule30EvenModeRigidityResearch']:
        assert g['elapsed_seconds']<60 and g['peak_owned_rss_bytes']<4*1024**3
    if mod=='Rule30EvenModeRigidityResearch':
        assert sha=='38e74acb17c0ddc2b40dc92e49052cb567056621bb8b18e8e28e16983f4b452b'
        assert c['replay']=={'constants':17,'ok':True} and len(c['headlines'])==6
        assert any(h['name']==mod+'.actual_even_plateau_or_clock_rigidity' for h in c['headlines'])
    if mod=='Rule30CoupledGerms':
        assert sha=='19eb466ca6dc36f0df1a51ad802f61f7a11aee4c32fd256f11b55817dc93090d'
        assert c['replay']=={'constants':33,'ok':True} and len(c['headlines'])==7
        assert not f['new_result_claimed_by_this_agent']
meta=data('work/external-germs-source.json')
assert meta['head_commit']=='de833dae04e9bb5e6e7e62add7b304a70f6532a7'
assert meta['external_proof_adopted'] and not meta['pending_full_kernel_replay']
assert meta['author']=='Elijah08-GIT with OpenAI Codex'
audit=data('work/mode-witness-audit.json')
assert audit['passed'] and not audit['Lean_verified'] and not audit['uniform_observer_refuted']
assert [x['rows'] for x in audit['reports']]==[192,960]
assert sum(x['literal_cell_updates'] for x in audit['reports'])==12369920
for x in audit['reports']:
    assert x['all_degree_le_two_moments_zero'] and x['target_xor']==1
    assert hashlib.sha256(read('work/mode-quadratic-negative-P'+str(x['clock'])+'.json')).hexdigest()==x['witness_sha256']
controls=data('work/even-mode-controls.json');assert controls['passed']
assert len(controls['reports'])==8
for x in controls['reports']:
    assert (x['qualifying_walks']==0)==(x['clock']%2==0)
for name in ['mode_coordinates','even_mode_controls','audit_mode_witnesses']:guard(name)
mode=data('work/mode-coordinate-probe.json')
assert not mode['Lean_verified'] and not mode['uniform_observer_proved']
assert [x['quadratic_negative_size'] for x in mode['reports'][-2:]]==[192,960]
s=data('summary.json')
assert s['new_module_declarations']==17 and s['external_module_declarations']==33
assert s['even_clock_OR_rigidity_uniformly_proved'] and s['newer_profile_period_premise_removed']
for n in ['external_work_claimed_as_ours','mode_observer_uniformly_proved','parent_bit_observer_proved',
          'fixed_center_bridge_proved','full_problem_solved','new_prize_submission',
          'new_pull_request','Wolfram_backend_verified']:assert not s[n],n
count=archives=0
for old in r.parent.glob('*/artifacts.json'):
    if old.parent.name in {'20261024-seven','20261025-round2','20261025-round2-review',r.name}:continue
    files=json.loads(old.read_bytes())['files']
    for n,h in files.items():assert hashlib.sha256((old.parent/n).read_bytes()).hexdigest()==h,(old.parent.name,n)
    count+=len(files);archives+=1
assert (count,archives)==(2963,35)
for n in m:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(m),
 'new_declarations':17,'external_declarations':33,'prior_hashes_unchanged':count,
 'mode_observer_proved':False,'full_problem_solved':False}))
