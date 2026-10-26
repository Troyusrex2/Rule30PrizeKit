"""Audit publication bytes and saved evidence; not a new kernel replay."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip());prefix=root.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (root/n).read_bytes()
def data(n):return json.loads(read(n))
def sha(b):return hashlib.sha256(b).hexdigest()
manifest=data('artifacts.json')['files']
for n,h in manifest.items():
    assert (root/n).resolve().is_relative_to(root) and sha(read(n))==h,n
s=data('summary.json');pin=s['official_pin'];checker=s['checker_sha256']
assert pin=='5473ffd075f63c9d626e63b8455805d4831b39ca'
assert sha(subprocess.check_output(['git','show',pin+':Check.lean'],cwd=repo))==checker=='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
counts={'CedarMarkerReturnTwo':45,'CedarReturnEightReduction':26,'PrizeSafetyBridge':100,'ResetExcursionControl':6,'RootOrientedHeight':13}
assert s['new_root_replayed_modules']==counts and s['new_root_replayed_declarations']==190
checks=dict(counts,Rule30CommonPastResearch=100,Rule30ColumnReaderResearch=119)
for module,count in checks.items():
    directory='work/oriented' if module=='RootOrientedHeight' else 'work/root'
    src=read(directory+'/'+module+'.lean');r=data(directory+'/formal/'+module+'/report.json');c=r['checker']
    assert sha(src)==r['source_sha256']==data(directory+'/sources.json')['sources'][module]['sha256']
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',src,re.M)
    assert r['passed'] and r['pin']==pin and r['checker_sha256']==checker
    assert c['module']==module and c['claim']=='partial' and c['importsStatements']
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True}
    assert not c['newAxioms'] and not c['verifiedTargets'] and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    g=data(directory+'/evidence/replay-'+module+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert g['elapsed_seconds']<=300 and g['peak_owned_rss_bytes']<=8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
review=data('work/source-review/review.json')
assert review['verdict']=='PASS_source_scope_only' and not review['semantic_defects'] and not review['duplicate_builds_performed']
assert review['report_sha256']==sha(read('REPORT.md')) and review['summary_sha256']==sha(read('summary.json'))
for module,item in review['sources'].items():
    directory='work/oriented' if module=='RootOrientedHeight' else 'work/root'
    assert item['source_sha256']==sha(read(directory+'/'+module+'.lean'))
    assert item['root_report_sha256']==sha(read(directory+'/formal/'+module+'/report.json'))
assert sha(read('work/external-pr31/MANIFEST.sha256'))==s['external_manifest_sha256']=='6f8c1278573d4d6f1047c3adde380e73582f1520b5d75ec79c4ae1a7c7edc848'
lines=read('work/external-pr31/MANIFEST.sha256').decode().splitlines();assert len(lines)==112
for line in lines:
    h,n=line.split('  ',1);assert sha(read('work/external-pr31/'+n))==h,n
for module,count in s['external_independent_worker_modules'].items():
    r=data('work/external-pr31/formal/'+module+'/report.json');c=r['checker']
    assert r['source_sha256']==sha(read('work/external-pr31/'+module+'.lean')) and r['pin']==pin and r['checker_sha256']==checker
    assert c['verdict']=='pass' and c['replay']=={'constants':count,'ok':True} and not c['newAxioms'] and not c['verifiedTargets']
    assert all(h['ok'] and h['typeMatches'] for h in c['headlines'])
ext=data('work/external-pr31/AUDIT.json');assert ext['verdict']=='PASS' and ext['upstream']['upstream_commit']==s['external_PR31_head']
assert ext['pumping_threshold']==10 and ext['kernel_base_case']==9 and ext['padded_bound_single_true']==9
assert ext['pumping_from_nine_negative_control_verified'] and ext['all_owned_jobs_terminal'] and not ext['reference_write']
provenance=data('work/review-provenance.json')
assert sha(read('work/bridge-worker/manifest.json'))==provenance['bridge_producer_manifest_sha256']=='13b54f5761590058506fd1b2580b79279a778c8c3d3a1d39d2eba88a87dd08d2'
producer=data('work/bridge-worker/manifest.json')['files'];assert len(producer)==52
for n,h in producer.items():assert sha(read('work/bridge-worker/'+n))==h,n
for module in ('PrizeSafetyBridge','ResetExcursionControl'):
    assert read('work/bridge-worker/'+module+'.lean')==read('work/root/'+module+'.lean')
height=data('work/height-diagnostic/result.json')
assert height['input_sha256']==sha(read('work/height-diagnostic/inputs/height_controls.json')) and not height['candidate_proved'] and not height['kernel_verified']
query=data('work/height-diagnostic/height2-result.json')
assert query['status']=='unsat' and query['width']==20 and query['period_return']==32 and not query['kernel_verified']
assert sha(read('work/height-diagnostic/height2-query.smt2').decode().replace('\r\n','\n').encode())==query['query_sha256']
for key in ['D3_proved','ReturnComplete_proved','ReaderComplete_proved','observer_proved','prize_problem_solved','new_pull_request','new_prize_submission','own_new_backend_verification_claimed','peer_binaries_reused','additional_root_kernel_replay_of_external_modules']:assert not s[key]
total=archives=0
for old in root.parent.glob('*/artifacts.json'):
    if old.parent.name in {root.name,'20261024-seven','20261025-round2','20261025-round2-review'}:continue
    files=json.loads(old.read_bytes())['files']
    for n,h in files.items():assert sha((old.parent/n).read_bytes())==h,(old.parent.name,n)
    total+=len(files);archives+=1
assert (total,archives)==(3809,46)
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(manifest),'new_root_declarations':190,'external_worker_declarations':218,'prior_hashes_unchanged':total,'prior_archives_unchanged':archives,'prize_solved':False}))
