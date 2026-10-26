"""Audit retained evidence, not a substitute for a fresh Lean replay."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip())
prefix=root.relative_to(repo).as_posix()
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
pub=data('work/public-source.json');assert pub['upstream_commit']==s['upstream_commit']=='16250824c5e80964495ca5ba6bb82fa69394a35a'
assert pub['upstream_repository']==s['upstream_repository']=='AIOvernight/Rule30PrizeKit'
for key,module,count,heads in [('WhiteEndNineChecks','Ruliology.CellularAutomata.Rule30Certificates.WhiteEndNineChecks',38,4),('Rule30WhiteEndNine','Ruliology.CellularAutomata.Rule30WhiteEndNine',29,3)]:
    src=read('work/'+key+'.lean');r=data('work/formal/'+key+'/report.json');c=r['checker']
    assert sha(src)==r['source_sha256']==pub['sources'][module]['sha256']
    assert r['passed'] and r['pin']==pin and r['checker_sha256']==checker
    assert c['module']==module and c['verdict']=='pass' and not c['newAxioms']
    assert c['replay']=={'constants':count,'ok':True}
    assert c['claim']=='partial' and c['importsStatements'] and not c['verifiedTargets']
    assert len(c['headlines'])==heads and all(h['ok'] and h['typeMatches'] for h in c['headlines'])
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',src,re.M)
    g=data('work/evidence/replay-'+key+'.guard.json')
    assert g['exit_code']==0 and g['guard_stop'] is None
    assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
    assert g['elapsed_seconds']<=300 and g['peak_owned_rss_bytes']<=8*1024**3 and g['minimum_system_available_bytes']>=2*1024**3
official=data('work/official-dependencies.json');assert official['pin']==pin and len(official['modules'])==7
for module,item in official['modules'].items():
    assert sha(subprocess.check_output(['git','show',pin+':'+item['path']],cwd=repo))==item['source_sha256'],module
overlay=data('work/overlay-receipt.json');assert overlay['passed'] and not overlay['reference_write']
assert overlay['pin']==pin and overlay['source_hashes_checked']==7 and len(overlay['copied'])==26
assert s['external_declarations_replayed']==67 and s['our_new_mathematical_results']==0
for key in ['uniform_certificate_existence_proved','observer_criterion_proved','full_problem_solved','new_prize_submission','new_pull_request','Wolfram_verification_claimed']:
    assert not s[key]
count=archives=0
for manifest in root.parent.glob('*/artifacts.json'):
    if manifest.parent.name in {root.name,'20261024-seven','20261025-round2','20261025-round2-review'}:continue
    old=json.loads(manifest.read_bytes())['files']
    for n,d in old.items():assert sha((manifest.parent/n).read_bytes())==d,(manifest.parent.name,n)
    count+=len(old);archives+=1
assert (count,archives)==(3570,43)
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(files),'external_declarations_replayed':67,'our_new_mathematics':0,'prior_hashes_unchanged':count,'prior_archives_unchanged':archives,'full_problem_solved':False}))
