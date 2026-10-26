"""Audit bytes and saved proof evidence; this is not a fresh Lean replay."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
parser=argparse.ArgumentParser();parser.add_argument('--staged',action='store_true');args=parser.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip());prefix=root.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (root/n).read_bytes()
def data(n):return json.loads(read(n))
def sha(b):return hashlib.sha256(b).hexdigest()
files=data('artifacts.json')['files']
for n,d in files.items():
    assert (root/n).resolve().is_relative_to(root)
    assert sha(read(n))==d,n
s=data('summary.json');pin=s['official_pin'];checker=s['checker_sha256']
assert pin=='5473ffd075f63c9d626e63b8455805d4831b39ca'
assert sha(subprocess.check_output(['git','show',pin+':Check.lean'],cwd=repo))==checker=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
expected={'RootEventHeight':43,'RootAntiPeriodHeight':26,'CedarD3Converse':8,'CedarTCObstruction':37,'CedarNo11011':31}
assert s['new_root_replayed_modules']==expected and s['new_root_replayed_declarations']==sum(expected.values())==145
assert not s['peer_binaries_reused'] and not s['fresh_dependency_replay_this_phase']
for module,count in expected.items():
    label='root-cylinder' if module.startswith('CedarTC') or module=='CedarNo11011' else 'root-height'
    path='work/'+label;src=read(path+'/'+module+'.lean');meta=data(path+'/sources.json')
    assert sha(src)==meta['sources'][module]['sha256']
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',src,re.M)
    r=data(path+'/formal/'+module+'/report.json');c=r['checker']
    assert r['passed'] and sha(src)==r['source_sha256'] and r['pin']==pin and r['checker_sha256']==checker
    assert c['module']==module and c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True}
    assert not c['newAxioms'] and not c['verifiedTargets'] and c['claim']=='partial' and c['importsStatements']
    assert all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    g=data(path+'/evidence/replay-'+module+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert g['elapsed_seconds']<=300 and g['peak_owned_rss_bytes']<=8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
    for dep,item in meta['previous_own_root_dependencies'].items():
        old=root.parent/'20261026-short-extension-proof/work/root/formal'/dep/'report.json'
        dr=json.loads(old.read_bytes())
        assert dr['source_sha256']==item['source_sha256'] and dr['compiled_sha256']==item['compiled_sha256']
        assert dr['checker']['replay']=={'constants':item['prior_root_replay_constants'],'ok':True}
provenance=data('work/provenance.json')
assert provenance['cedar_v03_hashes_verified']==256
assert provenance['cedar_v03_manifest_sha256']=='8916cfecdad9bca331f444bbf3e0bf9dadb0cae56cca0717e8ac844fdcc1361a'
for label in ('height','anti'):
    p='work/worker-'+label
    assert sha(read(p+'/manifest.json'))==provenance[label+'_worker']['manifest_sha256']
    worker=data(p+'/manifest.json')['files'];assert len(worker)==provenance[label+'_worker']['hashes_verified']
    for n,d in worker.items():assert sha(read(p+'/'+n))==d
for n,d in provenance['selected_cedar_files'].items():assert sha(read('work/cedar/'+n))==d
assert sha(read('work/source-review/manifest.json'))==provenance['source_review_manifest_sha256']=='8f0ffb73eda37ced75f0e5a8d233cc97216189fb38ef4574f232bac7714d91a8'
review_files=data('work/source-review/manifest.json')['files'];assert len(review_files)==7
for n,d in review_files.items():assert sha(read('work/source-review/'+n))==d
review=data('work/source-review/source-review.json')
assert review['status']=='PASS_source_scope_only' and not review['findings'] and not review['independent_build_or_checker_replay']
for n,item in review['sources'].items():assert item['sha256']==sha(read('work/root-cylinder/'+n))
for n in ('CedarTCObstruction','CedarNo11011'):
    assert read('work/cedar/'+n+'.lean')==read('work/root-cylinder/'+n+'.lean')
assert read('work/worker-height/RootEventHeight.lean')==read('work/root-height/RootEventHeight.lean')
assert read('work/worker-anti/RootAntiPeriodHeight.lean')==read('work/root-height/RootAntiPeriodHeight.lean')
cycles=data('work/diagnostics/cycle-audit.json');assert cycles['passed'] and not cycles['kernel_verified'] and not cycles['finite_white_counterexample']
assert sha(read('work/diagnostics/free_strip_safety.json'))==cycles['input_sha256']
assert [x['least_newest_period'] for x in cycles['audits']]==[17,32]
for x in cycles['audits']:assert x['safe_including_wrap'] and x['non8'] and x['avoids_11011'] and x['white_boundary_failures']
for key in ['d3_proved','global_safety_completeness_proved','fixed_center_observer_proved','prize_problem_solved','new_pull_request','new_prize_submission','Wolfram_verification_claimed']:assert not s[key]
count=archives=0
for manifest in root.parent.glob('*/artifacts.json'):
    if manifest.parent.name in {root.name,'20261024-seven','20261025-round2','20261025-round2-review'}:continue
    old=json.loads(manifest.read_bytes())['files']
    for n,d in old.items():assert sha((manifest.parent/n).read_bytes())==d,(manifest.parent.name,n)
    count+=len(old);archives+=1
assert (count,archives)==(3697,45)
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(files),'new_root_replayed_declarations':145,'prior_owned_hashes_unchanged':count,'prior_archives_unchanged':archives,'prize_problem_solved':False}))
