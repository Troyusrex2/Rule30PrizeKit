"""Audit exact working/staged archive bytes and proof/experiment scope."""
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
expected={
 'Rule30MaskedDefectResearch':(15,3,'bf9456b2d0aad25aea20013d69f5ebd0cf38b074a68710a4b343fe3b3f0859c3','masked-defect'),
 'Rule30Slip94Research':(192,3,'141ce2d843bdcc7d37631d30d8522d36ea680e70248bcf7a892029b2aae8749e','slip94'),
 'Rule30VerifiedCoupledGoldenExtract':(47,4,'fb04bd35dbe7eda540c89affed8c03adfabc3ee063da5ab8f0070b752fe2d8c1','coupled-golden'),
 'Rule30CoupledSixWordResearch':(16,3,'e1f8c88120ea7bb274d570958af00b978b88c3eb7077b8ad4f0fd66db3e0718e','sixword'),
 'Rule30SingleSlipExclusionResearch':(13,3,'83bccdfc51512e8f8b67a5d07f01f1c2b39b316673fb52b645829690a90d4015','single-slip-exclusion')}
for module,(count,heads,sha,label) in expected.items():
    source=read('work/'+module+'.lean')
    assert hashlib.sha256(source).hexdigest()==sha,module
    assert not re.search(rb'^\s*(?:axiom|sorry)\b|\b(?:native_decide|bv_decide)\b|decide\s*\+native',source,re.M),module
    r=data('work/formal/'+module+'/report.json')
    assert r['source_sha256']==sha and r['passed'] and r['checker_unchanged']
    assert not r['full_problem_solved']
    assert r['kit_commit']=='0090056412733accaa27643d3cbbf982104f2251'
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    c=r['check'];assert c['verdict']=='pass' and not c['newAxioms']
    assert c['replay']=={'constants':count,'ok':True}
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    g=data('work/'+label+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
intake=data('work/intake-seven.json')
assert len(intake['responses'])==7
for r in intake['responses']:
    for name,sha in r['files'].items():
        assert hashlib.sha256(read('work/snapshots/'+r['response']+'/'+name)).hexdigest()==sha
comparison=data('work/reproduction-comparison.json')
assert comparison['all_equal_after_runtime_normalization'] and len(comparison['checks'])==19
assert all(c['equal'] for c in comparison['checks']) and not comparison['Lean_verified']
num='work/remote-numerical/'
assert data(num+'right-admissibility.json')['first_unsat_width_with_right_admissibility']==5
assert data(num+'sanity-holdout.json')['complete_annuli']==257
assert not data(num+'sanity-holdout.json')['fixed_M_failures']
assert data(num+'swarm-phase-test.json')['four_step_violations']==52271
profile=data(num+'wiki-closed-profile.json')
assert profile['full_profile_cycle']['period']==28 and profile['full_profile_cycle']['black_per_period']==6
assert not profile['Lean_verified'] and not profile['full_problem_solved']
summary=data('summary.json')
assert not summary['full_problem_solved'] and not summary['new_prize_submission']
assert summary['all_seven_tested'] and summary['prior_hashes_unchanged']==1234
for name in manifest:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(name),re.I),name
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(manifest),
 'modules_fully_replayed':5,'new_research_modules':3,'responses':7,'full_problem_solved':False}))
