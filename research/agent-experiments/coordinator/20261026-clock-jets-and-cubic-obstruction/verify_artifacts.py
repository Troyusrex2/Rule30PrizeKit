from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
r=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=r,text=True).strip())
prefix=r.relative_to(repo).as_posix()
def read(n):
    return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (r/n).read_bytes()
def data(n):return json.loads(read(n))
manifest=data('artifacts.json')['files']
for n,h in manifest.items():assert hashlib.sha256(read(n)).hexdigest()==h,n
summary=data('summary.json');inv=data('work/publication-inventory.json')
expected_pin='0090056412733accaa27643d3cbbf982104f2251'
expected_checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
official=subprocess.check_output(['git','show',expected_pin+':Check.lean'],cwd=repo)
assert hashlib.sha256(official).hexdigest()==expected_checker
assert len(inv['new_modules'])==32 and inv['new_declarations']==301
for item in inv['new_modules']:
    m=item['module'];source=read('work/'+m+'.lean');sha=hashlib.sha256(source).hexdigest()
    assert sha==item['sha256']
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native|skipKernel',source,re.M)
    j=data('work/formal/'+m+'/report.json');c=j['check']
    assert j['passed'] and j['checker_unchanged'] and j['source_sha256']==sha
    assert j['kit_commit']==expected_pin and j['checker_sha256']==expected_checker
    assert not j['full_problem_solved'] and c['verdict']=='pass' and not c['newAxioms']
    assert c['replay']=={'ok':True,'constants':item['declarations']}
    assert len(c['headlines'])==item['headlines'] and all(x['ok'] and x['typeMatches'] for x in c['headlines'])
    g=data('work/evidence/replay-'+m+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert g['elapsed_seconds']<60 and g['peak_owned_rss_bytes']<4*1024**3
    assert g['minimum_system_available_bytes']>=2*1024**3
batch=data('work/certificate-batch-progress.json')
assert len(batch)==26 and all(x['exit_code']==0 for x in batch)
audit=data('work/orbit-witness-audit.json')
assert audit['passed'] and audit['witness_rows']==18528 and audit['canonical_word_width']==105
assert audit['all_initial_words_canonical'] and audit['all_initial_words_distinct']
assert audit['all_rows_return_after_full_cycle'] and audit['full_cycle']==128
assert audit['literal_rule30_cells']==249016320 and audit['head_monomials_independently_checked']==349633
assert audit['all_constant_to_cubic_head_moments_zero'] and audit['penultimate_initial_bits_xor']==1
assert not audit['Lean_verified'] and not audit['canonical_observer_refuted'] and not audit['full_problem_solved']
g=data('work/evidence/audit_orbit_witness.guard.json');assert g['exit_code']==0 and g['guard_stop'] is None
cycles=data('work/orbit-negative-certificate.json')
assert cycles['selected_orbits']==290 and cycles['selected_rows']==18528
assert len(cycles['orbit_certificate'])==290 and sum(o['period'] for o in cycles['orbit_certificate'])==18528
assert max(o['parent_width'] for o in cycles['orbit_certificate'])==104
large=data('work/clock-cubic-large.json');assert large['controls']==70 and large['negative_found']
assert large['reports'][-1]['clock']==64 and large['reports'][-1]['cubic_rank']==43745
assert not large['reports'][-1]['parent_bit_recoverable']
wl=data('work/wolfram-control.json');assert wl['passed'] and wl['initial_rows']==1022
assert wl['identity_comparisons']==29240 and not wl['Wolfram_backend_verification']
failure=data('work/failed-attempts/Rule30CubicWitnessData/replay-Rule30CubicWitnessData.guard.json')
assert failure['guard_stop']=='owned_tree_memory' and failure['exit_code']!=0
assert summary['packed_finite_certificate_kernel_checked'] and summary['actual_cycle_and_all_phase_canonical_semantics_kernel_checked']
assert not summary['complete_cubic_impossibility_theorem_kernel_checked']
assert not summary['parent_bit_observer_proved'] and not summary['full_problem_solved']
assert not summary['new_prize_submission'] and not summary['Wolfram_backend_verified']
skip={'20261024-seven','20261025-round2','20261025-round2-review',r.name}
count=archives=0
for old in r.parent.glob('*/artifacts.json'):
    if old.parent.name in skip:continue
    files=json.loads(old.read_bytes())['files']
    for n,h in files.items():assert hashlib.sha256((old.parent/n).read_bytes()).hexdigest()==h,(old.parent.name,n)
    count+=len(files);archives+=1
assert count==2334 and archives==33
for n in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(manifest),
 'new_modules':32,'new_declarations':301,'prior_hashes_unchanged':count,
 'full_cubic_impossibility_kernel_theorem':False,'full_problem_solved':False}))
