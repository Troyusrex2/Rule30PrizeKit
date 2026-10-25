"""Read-only source, scope and exact byte audit; optionally read actual index blobs."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent
staged='--staged' in sys.argv
repo=next(p for p in root.parents if (p/'.git').exists())
def read(p):
    if staged:return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
def obj(p):return json.loads(read(p))
m=obj(root/'artifacts.json');s=obj(root/'summary.json');w=root/'work'
assert set(m['files'])|{'artifacts.json'}=={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
for name,sha in m['files'].items():
    raw=read(root/name)
    assert hashlib.sha256(raw).hexdigest()==sha,name
    if name.endswith('.py'):ast.parse(raw,filename=name)
    if name.endswith('.json'):json.loads(raw)
assert not s['full_problem_solved'] and not s['prize_api_submitted']
assert not s['all_width_staggered_classification'] and not s['canonical_observer_refuted']
assert s['prior_hashes_unchanged']==889
for name,count,heads in [('Rule30WeightedCellResearch',97,7),('Rule30FiniteRectangleResearch',72,5)]:
    source=read(w/(name+'.lean'));r=obj(w/'evidence'/name/'report.json');c=r['check']
    assert hashlib.sha256(source).hexdigest()==r['source_sha256']
    assert r['kit_commit']==s['kit_commit'] and r['checker_unchanged']
    assert r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True}
    assert not c['newAxioms'] and c['importsStatements'] and len(c['headlines'])==heads
    assert all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    assert all(cmd['exit_code']==0 for cmd in r['commands'])
    assert not re.search(rb'\b(sorry|axiom|native_decide|bv_decide)\b|skipKernel|decide\s*\+native',source)
    assert b'Mathlib' not in source
for job in s['guarded_jobs']:
    g=obj(w/'evidence'/(job+'.guard.json'))
    assert g['exit_code']==0 and g['guard_stop'] is None,job
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3
    assert g['minimum_system_available_bytes']>=2*1024**3
for folder in ['attempt01-unreduced-row-lookups','attempt02-ac-normalization-timeout','attempt03-flat-ac-timeout']:
    g=obj(w/'failed'/folder/'guard.json')
    assert g['exit_code']!=0 and g['guard_stop'] is None
clock=obj(w/'clock-independent-verification.json')
assert clock['all_dimensions_match'] and clock['cyclic_states']==26676
assert clock['input_sha256']==hashlib.sha256(read(w/'clock-charge.json')).hexdigest()
weighted=obj(w/'weighted-independent-verification.json')
assert weighted['pass'] and len(weighted['Rule30_periodic_weight_controls'])==64
assert weighted['source_sha256']==hashlib.sha256(read(w/'Rule30WeightedCellResearch.lean')).hexdigest()
rect=obj(w/'rectangle-independent-verification.json')
assert rect['pass'] and rect['whole_line_controls']==2080 and rect['missing_shield_control_first_failure']==2
assert rect['source_sha256']==hashlib.sha256(read(w/'Rule30FiniteRectangleResearch.lean')).hexdigest()
print(json.dumps({'pass':True,'staged_blobs':staged,'selected_hashes':len(m['files']),
                  'weighted_constants':97,'rectangle_constants':72,'full_problem_solved':False}))
