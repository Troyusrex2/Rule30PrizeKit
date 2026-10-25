"""Read-only artifact, staged-blob, full-replay and notebook-scope audit."""
from pathlib import Path
import ast,gzip,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent;staged='--staged' in sys.argv
repo=next((p for p in root.parents if (p/'.git').exists()),None)
def read(p):
    if staged:
        assert repo
        return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
def obj(p):return json.loads(read(p))
m=obj(root/'artifacts.json')
for f,h in m['files'].items():
    p=(root/f).resolve();assert p.is_relative_to(root.resolve())
    assert hashlib.sha256(read(p)).hexdigest()==h,f
assert {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}==set(m['files'])|{'artifacts.json'}
s=obj(root/'summary.json');w=root/'work';total=0
assert not s['full_problem_solved'] and s['new_unique_kernel_replayed_constants']==173
assert not any(s[k] for k in ['density_bound_proved','finite_right_realizability_proved','C3_proved','C4_proved','prize_api_submitted','fresh_human_consent_received_for_this_draft'])
for n,meta in s['modules'].items():
    r=obj(w/'evidence'/n/'report.json');c=r['check']
    assert hashlib.sha256(read(w/(n+'.lean'))).hexdigest()==r['source_sha256']==meta['source_sha256']
    assert r['checker_unchanged'] and r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and c['importsStatements'] and c['replay']['ok'] and not c['newAxioms']
    assert all(h['ok'] and h['found'] and h['typeMatches'] for h in c['headlines'])
    assert c['replay']==meta['replay'] and r['kit_commit']==s['prior_kit_commit']
    assert read(w/'evidence'/n/'build.log')==b''
    assert all(x['exit_code']==0 for x in r['commands']);total+=c['replay']['constants']
assert total==173
for folder,pin in [('catalog-evidence',s['prior_kit_commit']),('catalog-current-evidence',s['current_kit_commit'])]:
    r=obj(w/folder/'report.json');c=r['check']
    assert hashlib.sha256(read(w/'Rule30DelayedDefectPeriods.lean')).hexdigest()==r['source_sha256']==s['catalog_source_sha256']
    assert r['kit_commit']==pin and r['checker_unchanged']
    assert c['verdict']=='pass' and c['replay']=={'constants':173,'ok':True} and not c['newAxioms']
    assert all(h['ok'] for h in c['headlines']) and all(x['exit_code']==0 for x in r['commands'])
r=obj(w/'evidence/Rule30Submission/report.json');c=r['check']
assert hashlib.sha256(read(w/'Rule30Submission.lean')).hexdigest()==r['source_sha256']==s['essay_source_sha256']
assert r['kit_commit']==s['current_kit_commit'] and r['checker_unchanged']
assert c['verdict']=='pass' and c['replay']=={'constants':173,'ok':True} and not c['newAxioms']
assert all(h['ok'] for h in c['headlines']) and all(x['exit_code']==0 for x in r['commands'])
for job in s['final_jobs']:
    g=obj(w/'evidence'/(job+'.guard.json'));assert g['exit_code']==0 and g['guard_stop'] is None,job
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
assert len(s['final_jobs'])==18
for name in s['repaired_attempts']:
    g=obj(w/'evidence'/(name+'.guard.json'));assert g['exit_code']!=0 and g['guard_stop'] is None
graphraw=gzip.decompress(read(w/'cyclic-depth.json.gz'));assert hashlib.sha256(graphraw).hexdigest()==s['cyclic_graph_raw_sha256']
graph=json.loads(graphraw);audit=obj(w/'cyclic-audit.json')
assert graph['nodes']==50001 and graph['maximum_period']==112 and graph['stop']=='node_cap'
assert len(graph['records'])==audit['verified_parent_edges']==49997
assert audit['minimum_including_bases']=='1/7' and len(audit['even_phase_witness_path'])==360
assert audit['minimum_new_ancestors_by_temporal_parity']['0']['density']=='5/28'
gold=obj(w/'golden-density.json');delayed=obj(w/'delayed-defects.json')
assert gold['samples']==10950 and gold['stop'] is None and gold['best']['cycle']['density']=='2/7'
assert len(delayed['records'])==537 and delayed['unknown']==0 and delayed['stop'] is None
assert delayed['best']['cycle']['density']=='3/14'
build=obj(w/'essay-build.json');fresh=obj(w/'essay-fresh-check.json');preview=obj(w/'preview-controls.json')
assert build['kernelCheckSuccess'] and build['sourceRoundTrip'] and '173' in build['kernelCheck']
assert fresh['freshKernelEvaluation'] and fresh['kernelCheckSuccess'] and fresh['isLeanEnvironment'] and fresh['inputCells']==7 and fresh['sourceRoundTrip'] and fresh['singleSeedPrefixControl']
assert not build['submitted'] and not fresh['submitted']
assert read(w/'Rule30Submission.lean')==read(w/'notebook-extracted.lean')
assert build['sourceSHA256']==fresh['sourceSHA256']==s['essay_source_sha256']
assert hashlib.sha256(read(w/'delayed-defect-essay.nb')).hexdigest()==build['notebookSHA256']==fresh['notebookSHA256']==s['essay_notebook_sha256']
assert preview['pass'] and preview['independent_preview_cells']==805 and not preview['submitted']
pending=obj(root/'PENDING-REVIEW.json');assert not pending['fresh_human_consent_received'] and not pending['submitted']
pr=obj(w/'pr25-readback.json');assert pr['headRefOid']==s['catalog_head'] and pr['state']=='OPEN' and len(pr['files'])==3
pin=obj(w/'pin-change-audit.json');assert pin['new']==s['current_kit_commit'] and pin['checker_identical'] and not pin['proof_import_sources_changed']
refresh=obj(w/'refresh-result.json');assert refresh['kit']['commit']==s['current_kit_commit'] and refresh['count']==41 and not any(refresh[k] for k in ['new_entries','removed_ids','changed_entries'])
for p in root.rglob('*.py'):ast.parse(read(p),filename=str(p))
for p in w.glob('Rule30*.lean'):
    assert not re.search(rb'\b(sorry|axiom|native_decide|bv_decide)\b|decide\s*\+native|debug\.skipKernelTC',read(p)),p
for p in [root/'REPORT.md',root/'REPRODUCE.md']:
    for t in re.findall(r'\]\(([^)]+)\)',read(p).decode('utf-8')):
        if '://' not in t and not t.startswith('#'):assert (p.parent/t.split('#')[0]).resolve().exists()
print(json.dumps({'pass':True,'staged_blobs':staged,'hashed_files':len(m['files']),
 'unique_new_replayed_constants':173,'current_pin':s['current_kit_commit'],
 'fresh_notebook_checked':True,'prize_api_submitted':False,'full_problem_solved':False}))
