"""Read-only hashes, actual staged blobs, proof reports and finite-result scope."""
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
m=obj(root/'artifacts.json')
for name,h in m['files'].items():
    p=(root/name).resolve();assert p.is_relative_to(root.resolve())
    assert hashlib.sha256(read(p)).hexdigest()==h,name
assert {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}==set(m['files'])|{'artifacts.json'}
s=obj(root/'summary.json');w=root/'work'
assert not s['full_problem_solved'] and s['new_kernel_replayed_constants']==95
assert not s['C3_counterexample_found'] and not s['C3_proved']
total=0
for name in ['Rule30SpatialLiftingResearch','Rule30SpatialPeriodResearch']:
    r=obj(w/'evidence'/name/'report.json');c=r['check']
    assert hashlib.sha256(read(w/(name+'.lean'))).hexdigest()==r['source_sha256']
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and c['importsStatements']
    assert all(h['ok'] and h['found'] and h['typeMatches'] for h in c['headlines'])
    assert r['checker_unchanged'] and r['kit_commit']==s['kit_commit']
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert read(w/'evidence'/name/'build.log')==b''
    assert all(x['exit_code']==0 for x in r['commands']);total+=c['replay']['constants']
assert total==95
r=obj(w/'catalog-evidence/report.json');c=r['check']
assert hashlib.sha256(read(w/'Rule30SpatialPeriodLifting.lean')).hexdigest()==r['source_sha256']
assert c['verdict']=='pass' and c['replay']=={'constants':95,'ok':True} and not c['newAxioms']
assert r['checker_unchanged'] and r['kit_commit']==s['kit_commit'] and all(h['ok'] for h in c['headlines'])
assert all(x['exit_code']==0 for x in r['commands'])
for job in s['final_jobs']:
    g=obj(w/'evidence'/(job+'.guard.json'))
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
for attempt in s['repaired_initial_compile_attempts']:
    g=obj(w/'evidence'/(attempt+'.guard.json'));assert g['exit_code']==1 and g['guard_stop'] is None
ex=obj(w/'exhaustive-traps.json');wide=obj(w/'width24-traps.json')
assert ex['initial_rows']==2**20 and ex['entry_count']==26116 and ex['distinct_eventual_streams_examined']==408
assert ex['stop'] is None and wide['stop'] is None and len(wide['chunks'])==15
assert all(x['full_horizon_checked'] and x['entries_classified']==x['trap_entries'] and x['completed_time']==128 for x in wide['chunks'])
assert ex['entry_count']+sum(x['trap_entries'] for x in wide['chunks'])==418403
assert sum(wide['density_histogram_including_width20'].values())==954
assert wide['best_actual']['spatial_cycle']['density']=='2/7'
assert all(not x['spatial_cycle'].get('C3_positive_drift') for x in ex['representatives']+wide['new_representatives'])
assert obj(w/'backward-traps.json')['records']==[] and obj(w/'backward-beam.json')['records']==[]
guided=obj(w/'guided-preimages.json');assert len(guided['records'])==2048 and guided['unique_streams']==3
lift=obj(w/'period-lifting.json');assert lift['stop']=='uniform_period_28_counterexample' and lift['counterexample']['cycle']['period']==56
counter=obj(w/'period28-counterexample.json');assert len(counter['prefix'])==76 and counter['cycle']['period']==56 and counter['scalar_cells_checked']==166140
pr=obj(w/'pr24-readback.json');assert pr['headRefOid']==s['catalog_head'] and pr['state']=='OPEN' and len(pr['files'])==3
up=obj(w/'upstream-009005-commit.json');assert up['sha']==s['upstream_latest_seen'] and 'Closes #16' in up['commit']['message']
external=obj(w/'external-audit.json');assert external['status']=='Lean Verified' and not external['locally_replayed'] and not external['adopted_in_new_proof']
for p in root.rglob('*.py'):ast.parse(read(p),filename=str(p))
for p in [w/'Rule30SpatialLiftingResearch.lean',w/'Rule30SpatialPeriodResearch.lean',w/'Rule30SpatialPeriodLifting.lean']:
    assert not re.search(rb'\b(sorry|axiom|native_decide|bv_decide)\b|decide\s*\+native|debug\.skipKernelTC',read(p))
for p in [root/'REPORT.md',root/'REPRODUCE.md']:
    for t in re.findall(r'\]\(([^)]+)\)',read(p).decode()):
        if '://' not in t and not t.startswith('#'):assert (p.parent/t.split('#')[0]).resolve().exists()
print(json.dumps({'pass':True,'staged_blobs':staged,'hashed_files':len(m['files']),
                  'new_unique_replayed_constants':95,'finite_rows':2**24,'full_problem_solved':False}))
