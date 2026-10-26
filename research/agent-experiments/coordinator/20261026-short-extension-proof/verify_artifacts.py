"""Audit recorded proof evidence; does not replace a fresh full Lean replay."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip());prefix=root.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (root/n).read_bytes()
def data(n):return json.loads(read(n))
def sha(raw):return hashlib.sha256(raw).hexdigest()
files=data('artifacts.json')['files']
for n,d in files.items():
    assert (root/n).resolve().is_relative_to(root)
    assert sha(read(n))==d,n
s=data('summary.json');pin=s['official_pin'];checker=s['checker_sha256']
assert pin=='5473ffd075f63c9d626e63b8455805d4831b39ca'
assert sha(subprocess.check_output(['git','show',pin+':Check.lean'],cwd=repo))==checker=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert sha(read('work/worker/manifest.json'))==s['worker_manifest_sha256']=='1f5108cd5c5537d664c1fbf97c19b03617e3c0a547bb6b46218c5051309c73fb'
worker=data('work/worker/manifest.json')['files'];assert len(worker)==56
for n,d in worker.items():assert sha(read('work/worker/'+n))==d,n
freeze=data('work/root/source-freeze.json')
counts={'CedarSafetySoundness':137,'CedarSafetySemantics':75,'CedarSafetyBridge':8,'RootShortExtensionCore':36,'RootShortExtensionCases':232,'RootShortExtensionCertificate':1,'RootShortExtension':4,'CedarWhiteTransport':18,'RootD3Reduction':10}
for module,count in counts.items():
    location='root' if module in ['CedarWhiteTransport','RootD3Reduction'] else 'worker'
    src=read('work/'+location+'/'+module+'.lean')
    if location=='worker':assert sha(src)==freeze['files'][module+'.lean']
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',src,re.M)
    for runner in (['root','worker'] if location=='worker' else ['root']):
        r=data('work/'+runner+'/formal/'+module+'/report.json');c=r['checker']
        assert r['passed'] and sha(src)==r['source_sha256'] and r['pin']==pin and r['checker_sha256']==checker
        assert c['module']==module and c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True}
        assert not c['newAxioms'] and not c['verifiedTargets'] and c['claim']=='partial' and c['importsStatements']
        assert all(h['ok'] and h['typeMatches'] for h in c['headlines'])
        g=data('work/'+runner+'/evidence/replay-'+module+'.guard.json')
        assert g['exit_code']==0 and g['guard_stop'] is None
        assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
        assert g['elapsed_seconds']<=300 and g['peak_owned_rss_bytes']<=8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
review=data('work/d3-source-review.json')
assert review['status']=='PASS_source_scope_only' and not review['findings'] and not review['independent_additional_build']
assert review['source_sha256']==sha(read('work/root/RootD3Reduction.lean'))
d3=read('work/root/RootD3Reduction.lean').decode()
assert 'def D3Star : Prop :=' in d3 and 'theorem return_complete_of_d3 (hd : D3Star)' in d3
assert s['short_extension_proved'] and s['d3_implies_global_safety_completeness_proved']
assert s['fresh_root_replay_constants']==sum(counts.values())==521
assert s['new_module_declarations']==283 and s['existing_dependency_declarations']==238
for k in ['d3_proved','global_safety_completeness_proved','fixed_center_observer_proved','prize_problem_solved','new_prize_submission','new_pull_request','Wolfram_verification_claimed']:
    assert not s[k]
count=archives=0
for manifest in root.parent.glob('*/artifacts.json'):
    if manifest.parent.name in {root.name,'20261024-seven','20261025-round2','20261025-round2-review'}:continue
    old=json.loads(manifest.read_bytes())['files']
    for n,d in old.items():assert sha((manifest.parent/n).read_bytes())==d,(manifest.parent.name,n)
    count+=len(old);archives+=1
assert (count,archives)==(3591,44)
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(files),'new_declarations':283,'fresh_root_constants':521,'prior_hashes_unchanged':count,'prior_archives_unchanged':archives,'D3_proved':False,'prize_problem_solved':False}))
