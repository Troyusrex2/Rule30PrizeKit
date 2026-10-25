"""Read-only saved evidence audit. This does not run or replace Lean replay."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent
staged='--staged' in sys.argv
repo=next((p for p in root.parents if (p/'.git').exists()),None)
def read(p):
    if staged:
        assert repo is not None
        return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
manifest=json.loads(read(root/'artifacts.json'))
for name,sha in manifest['files'].items():
    p=(root/name).resolve()
    assert p.is_relative_to(root.resolve())
    assert hashlib.sha256(read(p)).hexdigest()==sha,name
assert {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}==set(manifest['files'])|{'artifacts.json'}
summary=json.loads(read(root/'summary.json')); proof=summary['proof']; check=proof['check']
assert not summary['full_problem_solved'] and summary['new_kernel_verified_declarations']==56
assert check['verdict']=='pass' and check['replay']=={'constants':56,'ok':True} and not check['newAxioms']
assert check['importsStatements'] and all(h['ok'] and h['found'] and h['typeMatches'] for h in check['headlines'])
assert len(check['headlines'])==4 and proof['checker_unchanged']
assert proof['kit_commit']=='3eca23c0a9fa6b153313655e6d51835406c2d06e'
assert proof['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
source=read(root/'work/Rule30DyadicSourceResearch.lean')
assert hashlib.sha256(source).hexdigest()==proof['source_sha256']
assert not re.search(rb'\b(sorry|axiom|native_decide|bv_decide)\b|decide\s*\+native|debug\.skipKernelTC',source)
assert read(root/'work/evidence/Rule30DyadicSourceResearch/build.log')==b''
for stage in proof['commands']: assert stage['exit_code']==0
for job in summary['jobs']:
    g=json.loads(read(root/'work/evidence'/(job+'.guard.json')))
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3
    assert g['minimum_system_available_bytes']>=2*1024**3
for p in root.rglob('*.py'): ast.parse(read(p),filename=str(p))
for p in root.rglob('*.md'):
    for target in re.findall(r'\]\(([^)]+)\)',read(p).decode('utf-8')):
        if '://' in target or target.startswith('#'): continue
        q=(p.parent/target.split('#')[0]).resolve()
        assert q.exists(),(p,target)
wall=json.loads(read(root/'work/number-wall.json'))
center=read(root/'work/center-65536.bin')
assert len(center)==65536 and set(center)=={0,1}
assert hashlib.sha256(center).hexdigest()==wall['center_sha256']
assert wall['controls']=={'exhaustive_bm_determinants':5120,'leibniz':4096,'physical_steps':512,
                         'direct_wall_determinants':4288,'jacobi_identities':260096}
for name,result in wall['sequences'].items():
    assert hashlib.sha256(read(root/'work'/(name+'-leading.bin'))).hexdigest()==result['leading_sha256']
assert all(x['training_conflicts']>0 for x in wall['sequences']['rule30']['coarse_patch_prediction'].values())
independent=json.loads(read(root/'work/independent-controls.json'))
assert independent['all_passed'] and len(independent['exact_contradictions'])==8
s90=json.loads(read(root/'work/source90.json'))
assert s90['counterexample_to_odd_boundary_survival']=={'time':7,'center':0,'outer':1,'interior':1}
outer=read(root/'work/outer90-65536.bin'); inner=read(root/'work/interior90-65536.bin')
assert len(outer)==len(inner)==len(center)
for n,(c,a,b) in enumerate(zip(center,outer,inner)):
    assert a==int(n>0 and n&(n+1)==0)
    assert c==(int(n==0)^a^b)
control=json.loads(read(root/'work/selected-events-control.json'))
assert control['all_passed'] and control['events_checked']==21810 and control['binomial_mask_crosschecks']==1858
assert all(len(x['sources'])==1 for x in control['records'])
refresh=json.loads(read(root/'work/refresh-result.json'))
assert refresh['count']==45 and not any(refresh[k] for k in ['new_entries','removed_ids','changed_entries'])
print(json.dumps({'pass':True,'staged_blobs':staged,'hashed_files':len(manifest['files']),
                  'kernel_replayed_constants':56,'full_problem_solved':False},indent=2))
