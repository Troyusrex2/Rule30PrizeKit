"""Read-only proof, scope, guard and byte-integrity audit; optional actual index."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent;staged='--staged' in sys.argv
repo=next((p for p in root.parents if (p/'.git').exists()),None)
def read(p):
    if staged:return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
def obj(p):return json.loads(read(p))
m=obj(root/'artifacts.json');s=obj(root/'summary.json');w=root/'work'
assert set(m['files'])|{'artifacts.json'}=={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
for f,h in m['files'].items():
    p=(root/f).resolve();assert p.is_relative_to(root.resolve());raw=read(p)
    assert hashlib.sha256(raw).hexdigest()==h,f
    if p.suffix=='.py':ast.parse(raw,filename=f)
    if p.suffix=='.json':json.loads(raw)
assert not any(s[k] for k in ['full_problem_solved','prize_api_submitted','fresh_notebook_verified',
 'nonlocal_invariants_excluded','canonical_only_invariants_excluded','companion_and_ports_counted_as_independent_results'])
assert s['core_replayed_constants']==207 and s['general_companion_replayed_constants']==189
assert s['prior_hashes_unchanged']==786 and s['four_step_cyclic_scope']
checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
checks=[('evidence/Rule30ProductConservationResearch','Rule30ProductConservationResearch.lean',189),
 ('evidence/Rule30ProductParityResearch','Rule30ProductParityResearch.lean',207),
 ('catalog-evidence','Rule30ProductParity.lean',207),
 ('essay-draft/evidence/Rule30Submission','essay-draft/Rule30Submission.lean',207)]
for folder,name,count in checks:
    r=obj(w/folder/'report.json');c=r['check']
    assert r['source_sha256']==hashlib.sha256(read(w/name)).hexdigest()
    assert r['checker_sha256']==checker and r['checker_unchanged'] and r['kit_commit']==s['kit_commit']
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True}
    assert c['importsStatements'] and not c['newAxioms'] and len(c['headlines'])==4
    assert all(h['ok'] and h['found'] and h['typeMatches'] for h in c['headlines'])
    assert all(a['exit_code']==0 for a in r['commands'])
    assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|skipKernel|decide\s*\+native',read(w/name).decode('utf-8'))
core=read(w/'Rule30ProductParityResearch.lean').decode('utf-8')
assert 'Mathlib' not in core and core.replace('Rule30ProductParityResearch','Ruliology.CellularAutomata.Rule30ProductParity')==read(w/'Rule30ProductParity.lean').decode('utf-8')
standalone='import Rule30PrizeKit\n'+core[len('module\n'):]
standalone=standalone.replace('public import ','import ').replace('@[expose] public section\n','').replace('Rule30ProductParityResearch','Rule30Submission')
assert standalone==read(w/'essay-draft/Rule30Submission.lean').decode('utf-8')
md=read(w/'essay-draft/essay.md').decode('utf-8');marker='LeanImportString[(*Iconize["Lean source"]*)'
assert md.count(marker)==1
encoded=md.split(marker,1)[1].split(', "ProjectDir" -> $Rule30PrizeKit]',1)[0]
assert json.loads(encoded)==standalone
assert obj(w/'essay-draft/exploration-check.json')['pass']
assert not obj(w/'essay-draft/preparation.json')['built_notebook']
for folder,jobs in [('',s['guarded_jobs']),('essay-draft',['replay-Rule30Submission','check_exploration']),
                    ('half-history',['canonical_half_control','half_followup'])]:
    for job in jobs:
        g=obj(w/folder/'evidence'/(job+'.guard.json'))
        assert g['exit_code']==0 and g['guard_stop'] is None,(folder,job)
        assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
failed=obj(w/'evidence/attempt04-core-omega/guard.json')
assert failed['guard_stop']=='system_available_memory' and failed['exit_code']!=0
manual=obj(w/'evidence/attempt04-core-omega/manual-stop.json')
assert not manual['manual_stop_executed'] and manual['authoritative_guard_stop']==failed['guard_stop']
for f in ['attempt01-pointwise-unfold','attempt03-cycle-type','attempt05-core-congruence']:
    g=obj(w/'evidence'/f/'guard.json');assert g['exit_code']!=0 and g['guard_stop'] is None
intermediate=read(w/'evidence/intermediate135-universe-headlines/check.log').decode('utf-8')
ic=json.loads(next(line for line in reversed(intermediate.splitlines()) if line.startswith('{')))
assert ic['replay']=={'constants':135,'ok':True} and ic['verdict']=='fail'
pr=obj(w/'pr27-readback.json');assert pr['pass'] and pr['head']==pr['remote_head']==pr['PR']['headRefOid']==s['catalog_head']
assert pr['source_sha256']==hashlib.sha256(read(w/'Rule30ProductParity.lean')).hexdigest()
assert pr['PR']['body'].replace('\r\n','\n').strip()==read(w/'PR-BODY.md').decode('utf-8').strip()
assert {f['path'] for f in pr['PR']['files']}=={'lean/README.md','lean/Ruliology.lean','lean/Ruliology/CellularAutomata/Rule30ProductParity.lean'}
pc=obj(w/'paired-independent-verification.json');assert pc['all_dimensions_match'] and pc['scalar_rings']==5888
assert pc['input_sha256']==hashlib.sha256(read(w/'paired-charge.json')).hexdigest()
sv=obj(w/'seam-independent-verification.json');assert sv['short_deadline_failure_independently_confirmed'] and sv['scalar_inverse_controls']==93
assert sv['last_cell_corruptions_rejected']==93 and sv['input_sha256']==hashlib.sha256(read(w/'seam-probe.json')).hexdigest()
seam=obj(w/'seam-probe.json')['failure'];assert (seam['short']['U'],seam['short']['V'],seam['extended']['first_black_depth_beyond_V'])==(5,4,9)
half=obj(w/'half-history/canonical-half-followup.json')['records'][-1]
assert half['U']==88 and half['V']==87 and half['first_true_A_vs_fake_C_center_difference']==89
assert half['first_common_field_wedge_violation_of_fake_difference']==[0,-80] and half['independent_canonical_certificate_passed']
print(json.dumps({'pass':True,'staged_blobs':staged,'hashes':len(m['files']),
  'core_replayed_constants':207,'general_companion_replayed_constants':189,
  'ports_not_double_counted':True,'full_problem_solved':False}))
