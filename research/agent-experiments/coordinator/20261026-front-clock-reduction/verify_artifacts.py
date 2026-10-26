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
expected={
 'Rule30FrontReductionResearch':(81,6,'c6e009b69c20c73aa4eff738be4e7fc04a5ffe280793e9af0af2a8877a304a3f','kernel'),
 'Rule30CommonPastResearch':(100,7,'17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3','dependency')}
for module,(count,heads,sha,label) in expected.items():
    source=read('work/'+module+'.lean');assert hashlib.sha256(source).hexdigest()==sha
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native',source,re.M)
    r=data('work/formal/'+module+'/report.json')
    assert r['passed'] and r['source_sha256']==sha and r['checker_unchanged'] and not r['full_problem_solved']
    assert r['kit_commit']=='0090056412733accaa27643d3cbbf982104f2251'
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    c=r['check'];assert c['verdict']=='pass' and not c['newAxioms'] and c['replay']=={'constants':count,'ok':True}
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    g=data('work/'+label+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
audit=data('work/independent-front-audit.json')
assert audit['passed'] and audit['clock_cases']==32 and audit['wrong_cut_rejected']
assert audit['clock_premises_cover_all_2288_tested_front_candidates'] and not audit['Lean_verified']
width=data('work/common-subset-probe-10.json')
assert width['nontrivial_modes_tested']==29185024 and width['common_survivors']==114488
assert not width['subset_failure_survivors'] and not width['unbounded_subset_preservation_proved']
front=data('work/temporal-front-14.json')
assert front['all_time_per_tested_prefix'] and not front['unbounded_front_stability_proved'] and not front['Lean_verified']
assert sum(r['varying_front_candidates'] for r in front['records'])==2288
assert max(r['prefix_bits'] for r in front['records'])==14
assert all(not r['uncovered_clock_cases'] and r['extensions_after_1_2_3_columns']==[0,0,0] for r in front['records'])
s=data('summary.json')
assert s['preservation_equivalent_to_front_stability'] and s['period_two_source_case_proved']
assert not s['collision_clock_proved'] and not s['unconditional_subset_preservation_proved']
assert not s['full_problem_solved'] and not s['new_prize_submission'] and s['prior_hashes_unchanged']==1621
for n in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':a.staged,'selected_hashes':len(manifest),'new_module_declarations':81,
                 'dependency_declarations':100,'unconditional_subset_preservation_proved':False,'full_problem_solved':False}))
