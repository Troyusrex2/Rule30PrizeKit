"""Read-only archive hash, finite-certificate, independent-check and scope audit."""
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
    raw=read(p);assert hashlib.sha256(raw).hexdigest()==h,f
    if p.suffix=='.py':ast.parse(raw,filename=f)
    if p.suffix=='.json':json.loads(raw)
    if p.suffix=='.jsonl':
        for line in raw.splitlines():json.loads(line)
assert not any(s[k] for k in ['full_problem_solved','Lean_verified',
  'canonical_N_equals_U_proved','canonical_observer_refuted',
  'finite_background_observer_refuted','prize_api_submitted'])
assert s['new_unique_replayed_constants']==0 and s['prior_hashes_unchanged']==726
v=obj(w/'common-independent-verification.json')
assert v['canonical_certificates_passed']==1120 and v['canonical_unique_pairs']==820
assert v['controls_passed']==11 and v['known_zero_output_witnesses']==8
assert v['corrupt_certificates_rejected']==1123 and v['physical_local_identities_replayed']==235841
for name,h in v['certificate_files_sha256'].items():assert hashlib.sha256(read(w/name)).hexdigest()==h
records=[]
for name in ['common-certificates.jsonl','deadline-certificates.jsonl']:
    cc=[json.loads(line) for line in read(w/name).splitlines()];records+=cc
    assert all(c['edge_forced'] and c['rows'] for c in cc)
    assert all(c['through']==c['U'] for c in cc) if name.startswith('deadline') else len(cc)==300
assert len({(c['U'],c['V']) for c in records})==820
deadline=obj(w/'deadline-probe.json');assert deadline['stop'] is None and len(deadline['records'])==820
iv=obj(w/'inverse-independent-verification.json')
assert iv['inverse_cases_independently_exhausted']==57 and iv['scalar_initial_words_tested']==14764
assert iv['input_sha256']==hashlib.sha256(read(w/'inverse-geometry-control.json')).hexdigest()
assert [(c['U'],c['V'],c['edge_prefix'],c['first_actual_disagreement']) for c in iv['collisions']]==[(4,3,0,6),(11,6,4,12)]
inv=obj(w/'inverse-geometry-control.json');assert inv['stop'] is None and len(inv['collisions'])==2
assert all(not c['N_equals_U_obstruction']['edge_forced'] for c in inv['collisions'])
assert inv['collisions'][1]['B_cells']==[-6,-5,-2,-1,1,5,6]
assert inv['collisions'][1]['trace']==[0,0,1,0,1,1,0,0,1,0,0,1]
for job in s['guarded_jobs']:
    g=obj(w/'evidence'/(job+'.guard.json'))
    assert g['exit_code']==0 and g['guard_stop'] is None,job
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3
    assert g['minimum_system_available_bytes']>=2*1024**3
failure=obj(w/'evidence/attempt01-assumed-counter/guard.json')
assert failure['exit_code']!=0 and failure['guard_stop'] is None
audit=obj(w/'external-change-audit.json')
assert not audit['adopted'] and audit['source_sha256']==hashlib.sha256(read(w/'external-017d83.lean')).hexdigest()
refresh=obj(w/'refresh-result.json');assert not refresh['new_entries'] and refresh['kit']['commit']==s['kit_commit']
for p in ['REPORT.md','REPRODUCE.md']:
    for link in re.findall(r'\]\(([^)]+)\)',read(root/p).decode('utf-8')):
        if '://' not in link:assert (root/link).exists(),link
print(json.dumps({'pass':True,'staged_blobs':staged,'hashes':len(m['files']),
  'independent_finite_certificates':1120,'unique_canonical_pairs':820,
  'new_unique_replayed_constants':0,'full_problem_solved':False}))
