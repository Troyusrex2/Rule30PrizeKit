"""Audit exact recorded proof/publication evidence; does not rerun Lean."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip())
prefix=root.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (root/n).read_bytes()
def data(n):return json.loads(read(n))
def sha(b):return hashlib.sha256(b).hexdigest()
files=data('artifacts.json')['files']
for n,d in files.items():
    assert (root/n).resolve().is_relative_to(root)
    assert sha(read(n))==d,n
s=data('summary.json');pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert s['official_pin']==pin and s['checker_sha256']==checker
assert sha(subprocess.check_output(['git','show',pin+':Check.lean'],cwd=repo))==checker
for module,count,heads in [('Rule30TraceEdge',14,2),('Rule30DividedDifference',198,7),('Rule30CommonGauge',174,5)]:
    src=read('work/'+module+'.lean');r=data('work/formal/'+module+'/report.json');c=r['checker']
    assert r['passed'] and r['source_sha256']==sha(src)
    assert r['pin']==pin and r['checker_sha256']==checker
    assert c['module']=='Ruliology.CellularAutomata.'+module and c['verdict']=='pass' and not c['newAxioms']
    assert c['replay']=={'constants':count,'ok':True}
    assert c['claim']=='partial' and c['importsStatements'] and not c['verifiedTargets']
    assert len(c['headlines'])==heads and all(x['ok'] and x['typeMatches'] for x in c['headlines'])
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',src,re.M)
    g=data('work/evidence/replay-'+module+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert g['elapsed_seconds']<=300 and g['peak_owned_rss_bytes']<=8*1024**3
    assert g['minimum_system_available_bytes']>=2*1024**3
official=data('work/official-dependencies.json');assert official['pin']==pin and len(official['modules'])==16
for m,item in official['modules'].items():
    raw=subprocess.check_output(['git','show',pin+':'+item['path']],cwd=repo)
    assert sha(raw)==item['source_sha256'],m
    if m.endswith('.Rule30TraceEdge'):assert raw==read('work/Rule30TraceEdge.lean')
overlay=data('work/overlay-receipt.json')
assert overlay['passed'] and overlay['pin']==pin and not overlay['reference_write']
assert overlay['source_hashes_checked']==16 and len(overlay['copied'])==60
assert len({e['artifact'] for e in overlay['copied']})==60
for e in overlay['copied']:assert e['artifact'].startswith('lib/Ruliology/') and re.fullmatch('[0-9a-f]{64}',e['sha256'])
review=data('work/cedar-pr26-source-review.json')
assert review['status']=='PASS_source_scope_only' and not review['findings']
assert review['sha256']==sha(read('work/Rule30DividedDifference.lean'))
assert review['root_reported_commit']==s['pr26_commit']
for pr,module in [(26,'Rule30DividedDifference'),(28,'Rule30CommonGauge')]:
    meta=data('work/PR'+str(pr)+'-metadata.json')
    assert meta['number']==pr and meta['state']=='OPEN' and meta['headRefOid']==s['pr'+str(pr)+'_commit']
    assert meta['body'].rstrip()==read('work/PR'+str(pr)+'-body.md').decode('utf-8').rstrip()
    raw=subprocess.check_output(['git','show',meta['headRefOid']+':lean/Ruliology/CellularAutomata/'+module+'.lean'],cwd=repo)
    assert raw==read('work/'+module+'.lean')
rb=data('work/PR-readback.json');assert rb['passed'] and rb['metadata_exact'] and len(rb['readbacks'])==6
for e in rb['readbacks']:
    assert e['commit']==s['pr'+str(e['pr'])+'_commit']
    assert sha(subprocess.check_output(['git','show',e['commit']+':'+e['path']],cwd=repo))==e['sha256']
src=read('work/Rule30DividedDifference.lean').decode('utf-8')
assert 'def ObserverCriterion : Prop :=' in src and 'set_option autoImplicit false' in src
assert 'theorem problem1_of_observerCriterion (hc : ObserverCriterion) : Rule30Prize.Problem1 :=' in src
assert s['criterion_to_EdgeObservable_proved'] and s['criterion_to_Problem1_proved']
assert s['canonical_mode_predicate_adapters_proved']
assert sum(s['modules'].values())-sum(s['previous_module_constants'].values())==23==s['added_declarations_including_definitions']
for k in ['observer_criterion_proved','full_problem_solved','new_prize_submission','new_pull_request',
          'maintainer_acceptance_claimed','new_Wolfram_verification_claim','full_catalog_root_build_run']:
    assert not s[k]
count=archives=0
for manifest in root.parent.glob('*/artifacts.json'):
    if manifest.parent.name in {root.name,'20261024-seven','20261025-round2','20261025-round2-review'}:continue
    old=json.loads(manifest.read_bytes())['files']
    for n,d in old.items():assert sha((manifest.parent/n).read_bytes())==d,(manifest.parent.name,n)
    count+=len(old);archives+=1
assert (count,archives)==(3530,42)
for n in files:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(files),
                  'changed_module_constants_replayed':372,'new_declarations_including_definitions':23,
                  'official_dependency_replayed_constants':14,'prior_hashes_unchanged':count,
                  'prior_archives_unchanged':archives,'observer_criterion_proved':False,'full_problem_solved':False}))
