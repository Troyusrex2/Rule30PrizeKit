"""Audit saved evidence and scope; never a substitute for kernel replay."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent;staged='--staged' in sys.argv
repo=next((p for p in root.parents if (p/'.git').exists()),None)
def read(p):
    if staged:
        assert repo
        return subprocess.check_output(['git','cat-file','blob',':'+p.relative_to(repo).as_posix()],cwd=repo)
    return p.read_bytes()
manifest=json.loads(read(root/'artifacts.json'))
for name,sha in manifest['files'].items():
    p=(root/name).resolve();assert p.is_relative_to(root.resolve())
    assert hashlib.sha256(read(p)).hexdigest()==sha,name
assert {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}==set(manifest['files'])|{'artifacts.json'}
summary=json.loads(read(root/'summary.json'))
assert not summary['full_problem_solved'] and summary['new_kernel_replayed_constants']==59
new_count=0
for name,meta in summary['modules'].items():
    report=json.loads(read(root/'work/evidence'/name/'report.json'));c=report['check']
    assert report['source_sha256']==hashlib.sha256(read(root/'work'/(name+'.lean'))).hexdigest()
    assert report['kit_commit']=='3eca23c0a9fa6b153313655e6d51835406c2d06e'
    assert report['checker_sha256']=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905' and report['checker_unchanged']
    assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and c['importsStatements']
    assert all(h['found'] and h['ok'] and h['typeMatches'] for h in c['headlines'])
    assert c['replay']==meta['replay'] and [h['name'] for h in c['headlines']]==meta['headlines']
    assert all(x['exit_code']==0 for x in report['commands'])
    assert read(root/'work/evidence'/name/'build.log')==b''
    if name!='Rule30DyadicSourceResearch':new_count+=c['replay']['constants']
assert new_count==59
for p in root.rglob('*.lean'):
    assert not re.search(rb'\b(sorry|axiom|native_decide|bv_decide)\b|decide\s*\+native|debug\.skipKernelTC',read(p))
for p in root.rglob('*.py'):ast.parse(read(p),filename=str(p))
for p in root.rglob('*.md'):
    for target in re.findall(r'\]\(([^)]+)\)',read(p).decode('utf-8')):
        if '://' not in target and not target.startswith('#'):
            assert (p.parent/target.split('#')[0]).resolve().exists(),(p,target)
for name in summary['jobs']:
    g=json.loads(read(root/'work/evidence'/(name+'.guard.json')))
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['elapsed_seconds']<300 and g['peak_owned_rss_bytes']<=8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
catalog=json.loads(read(root/'work/catalog-evidence/report.json'))
assert catalog['check']['verdict']=='pass' and catalog['check']['replay']=={'constants':56,'ok':True} and not catalog['check']['newAxioms']
assert hashlib.sha256(read(root/'work/catalog/Rule30RunBoundarySources.lean')).hexdigest()==catalog['source_sha256']
a=read(root/'work/Rule30DyadicSourceResearch.lean').decode('utf-8').split('@[expose] public section',1)[1]
b=read(root/'work/catalog/Rule30RunBoundarySources.lean').decode('utf-8').split('@[expose] public section',1)[1]
assert a==b.replace('Ruliology.CellularAutomata.Rule30RunBoundarySources','Rule30DyadicSourceResearch')
green=json.loads(read(root/'work/green-controls.json'))
assert green['all_passed'] and green['local_row_controls']==8192 and green['full_polynomial_convolutions']==257
assert len(green['dyadic_complete_splits'])==11 and all(r['shallow_parity']==1 and r['center']==(1^r['deep_parity']) for r in green['dyadic_complete_splits'])
deep=json.loads(read(root/'work/deep-channels.json'))
assert deep['all_passed'] and deep['sampled_terms']==797161 and deep['even_rho_checks']==5
assert deep['counterexample_to_first_even_depth_after_odd_rho']=={'H':16,'rho':7,'first_even_depth_above_rho':8,'actual_first_active_depth':14,'actual_first_odd_channel':18}
refresh=json.loads(read(root/'work/refresh-result.json'))
assert refresh['count']==41 and not refresh['new_entries'] and not refresh['changed_entries'] and len(refresh['removed_ids'])==4
print(json.dumps({'pass':True,'staged_blobs':staged,'hashed_files':len(manifest['files']),
                  'new_kernel_replayed_constants':59,'full_problem_solved':False},indent=2))
