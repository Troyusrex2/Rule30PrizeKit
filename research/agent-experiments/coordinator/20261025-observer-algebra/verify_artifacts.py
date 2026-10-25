"""Read-only hash, proof-source, full-replay and scope audit."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent;staged='--staged' in sys.argv
repo=next((p for p in root.parents if (p/'.git').exists()),None)
def read(p):
    if staged:
        assert repo
        return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
def obj(p):return json.loads(read(p))
m=obj(root/'artifacts.json');s=obj(root/'summary.json');w=root/'work'
assert set(m['files'])|{'artifacts.json'}=={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
for f,h in m['files'].items():
    p=(root/f).resolve();assert p.is_relative_to(root.resolve())
    assert hashlib.sha256(read(p)).hexdigest()==h,f
    if p.suffix=='.py':ast.parse(read(p),filename=f)
    if p.suffix=='.json':json.loads(read(p))
assert not any(s[k] for k in ['full_problem_solved','canonical_observer_refuted',
 'finite_background_observer_refuted','intermediate_and_catalog_rechecks_counted_again',
 'prize_api_submitted','new_barrier_essay_prepared','parity_arbitrary_width_classification_proved'])
assert s['new_unique_replayed_constants']==185 and s['prior_hashes_unchanged']==643
research=read(w/'Rule30ObserverBarrierResearch.lean').decode('utf-8')
catalog=read(w/'Rule30DividedDifference.lean').decode('utf-8')
marker='@[expose] public section'
assert research.replace('Rule30ObserverBarrierResearch','Ruliology.CellularAutomata.Rule30DividedDifference').split(marker,1)[1]==catalog.split(marker,1)[1]
assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|skipKernel|decide\s*\+native',catalog)
for folder,name in [('evidence/Rule30ObserverBarrierResearch','Rule30ObserverBarrierResearch.lean'),
                    ('catalog-evidence','Rule30DividedDifference.lean')]:
    r=obj(w/folder/'report.json');c=r['check']
    assert r['source_sha256']==hashlib.sha256(read(w/name)).hexdigest()
    assert r['kit_commit']==s['kit_commit'] and r['checker_unchanged']
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and c['replay']=={'constants':185,'ok':True}
    assert c['importsStatements'] and not c['newAxioms'] and len(c['headlines'])==11
    assert all(h['ok'] and h['found'] and h['typeMatches'] for h in c['headlines'])
    assert all(x['exit_code']==0 for x in r['commands'])
assert read(w/'evidence/Rule30ObserverBarrierResearch/build.log')==b''
for job in s['guards_normal']:
    g=obj(w/'evidence'/(job+'.guard.json'))
    assert g['exit_code']==0 and g['guard_stop'] is None,job
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3
    assert g['minimum_system_available_bytes']>=2*1024**3
for folder in ['attempt01-root-import','attempt02-core-not-built','attempt03-proof','attempt04-front-base']:
    g=obj(w/'evidence'/folder/'guard.json');assert g['exit_code']!=0 and g['guard_stop'] is None
for folder,n in [('intermediate150',150),('intermediate180',180)]:
    r=obj(w/'evidence'/folder/'replay/report.json')
    assert r['check']['replay']=={'constants':n,'ok':True}
pr=obj(w/'pr26-readback.json')
assert pr['pass'] and pr['head']==pr['remote_head']==pr['PR']['headRefOid']==s['catalog_head']
assert pr['source_sha256']==s['catalog_source_sha256']==hashlib.sha256(read(w/'Rule30DividedDifference.lean')).hexdigest()
assert pr['PR']['body'].replace('\r\n','\n').strip()==read(w/'PR-BODY.md').decode('utf-8').strip()
assert {f['path'] for f in pr['PR']['files']}=={'lean/README.md','lean/Ruliology.lean','lean/Ruliology/CellularAutomata/Rule30DividedDifference.lean'}
control=obj(w/'curvature-control.json');assert control['local_curvature_identity_checks']==512 and control['support_escape']
family=obj(w/'merging-backgrounds.json');assert len(family['records'])==8 and not family['canonical_observer_refuted']
assert all(r['time_checked']==128 and r['auxiliary_center_always_zero'] and r['all_gauge_wedges_zero']
           and not r['backgrounds_finite_at_time_zero'] for r in family['records'])
assert family['records'][0]['first_actual_recombination_center_difference']==7
parity=obj(w/'parity-independent-check.json');assert parity['pass'] and parity['scalar_ring_states_checked']==16382
assert parity['exact_saved_constraint_bases_match'] and parity['constant_plus_coboundary_spaces_match']
assert not parity['arbitrary_width_classification_proved'] and not parity['Lean_verified']
p=obj(w/'observer-preview.json');assert p['pass'] and p['first_physical_center_difference']==7
assert p['figure_sha256']==hashlib.sha256(read(w/'observer-barrier.png')).hexdigest()
assert all(row[19]==0 for row in p['auxiliary'])
assert p['physical_difference'][7][19]==1 and p['first_physicality_failure']==[4,-5]
snap=obj(w/'refresh-result.json');assert snap['count']==41 and not snap['new_entries'] and not snap['changed_entries']
for file in ['REPORT.md','REPRODUCE.md']:
    for href in re.findall(r'\]\(([^)]+)\)',read(root/file).decode('utf-8')):
        if '://' not in href:assert (root/href).exists(),href
print(json.dumps({'pass':True,'staged_blobs':staged,'hashes':len(m['files']),
                  'new_unique_replayed_constants':185,'full_problem_solved':False}))
