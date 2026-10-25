"""Read-only saved artifact and scope audit; does not replace Lean replay."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent;staged='--staged' in sys.argv
repo=next((p for p in root.parents if (p/'.git').exists()),None)
def read(p):
    if staged:
        assert repo
        return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
m=json.loads(read(root/'artifacts.json'))
for name,sha in m['files'].items():
    p=(root/name).resolve();assert p.is_relative_to(root.resolve())
    assert hashlib.sha256(read(p)).hexdigest()==sha,name
assert {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}==set(m['files'])|{'artifacts.json'}
summary=json.loads(read(root/'summary.json'))
assert not summary['full_problem_solved'] and summary['new_kernel_replayed_constants']==155
total=0
for name,meta in summary['modules'].items():
    r=json.loads(read(root/'work/evidence'/name/'report.json'));c=r['check']
    assert hashlib.sha256(read(root/'work'/(name+'.lean'))).hexdigest()==r['source_sha256']==meta['source_sha256']
    assert r['kit_commit']=='3eca23c0a9fa6b153313655e6d51835406c2d06e'
    assert r['checker_unchanged'] and r['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
    assert c['verdict']=='pass' and c['importsStatements'] and c['replay']['ok'] and not c['newAxioms']
    assert all(h['ok'] and h['found'] and h['typeMatches'] for h in c['headlines'])
    assert c['replay']==meta['replay'] and [h['name'] for h in c['headlines']]==meta['headlines']
    assert all(x['exit_code']==0 for x in r['commands'])
    assert read(root/'work/evidence'/name/'build.log')==b''
    total+=c['replay']['constants']
assert total==155
for name,meta in summary['reused_dependencies'].items():
    r=json.loads(read(root/'work/dependency-evidence'/(name+'.json')))
    assert hashlib.sha256(read(root/'work/dependency-source'/(name+'.lean'))).hexdigest()==meta['source_sha256']==r['source_sha256']
    assert r['check']['verdict']=='pass' and r['check']['replay']['ok'] and not r['check']['newAxioms']
for p in root.rglob('*.lean'):
    assert not re.search(rb'\b(sorry|axiom|native_decide|bv_decide)\b|decide\s*\+native|debug\.skipKernelTC',read(p))
for p in root.rglob('*.py'):ast.parse(read(p),filename=str(p))
for p in root.rglob('*.md'):
    for target in re.findall(r'\]\(([^)]+)\)',read(p).decode('utf-8')):
        if '://' not in target and not target.startswith('#'):
            assert (p.parent/target.split('#')[0]).resolve().exists(),(p,target)
for job in summary['jobs']:
    g=json.loads(read(root/'work/evidence'/(job+'.guard.json')))
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
echo=json.loads(read(root/'work/echo-operator.json'))
assert echo['controls']==10752 and not echo['full_problem_solved']
assert echo['generic_shortcut_counterexample']['row']==9 and echo['generic_shortcut_counterexample']['first_nonone_after_bound']==10
assert echo['canonical_shortcut_counterexample']['seed_time']==2 and echo['canonical_shortcut_counterexample']['first_nonone_after_bound']==12
anf=json.loads(read(root/'work/echo-anf.json'))
assert anf['direct_truth_table_controls']==1490 and len(anf['records'])==16
assert [x['degree'] for x in anf['records'] if not x['seedlow']]==[2,4,6,8,10,12,14,16]
assert [x['degree'] for x in anf['records'] if x['seedlow']]==[0,2,3,6,7,10,11,14]
controls=json.loads(read(root/'work/return-controls.json'))
assert controls['all_passed'] and not controls['full_problem_solved']
assert controls['checks']=={'physical_cells':4420,'prefix_periods':33024,'cut_flips':33024,
    'cut_window_sources':250,'allones_choose':2047,'selected_events_below_cut':22992,'direct_leading_binomial_terms':788}
assert all(x['even_leading_parity']==1 for x in controls['records'] if x['rho']%2==0)
refresh=json.loads(read(root/'work/refresh-result.json'))
assert refresh['count']==41 and not any(refresh[x] for x in ['new_entries','removed_ids','changed_entries'])
print(json.dumps({'pass':True,'staged_blobs':staged,'hashed_files':len(m['files']),
                  'new_kernel_replayed_constants':155,'full_problem_solved':False},indent=2))
