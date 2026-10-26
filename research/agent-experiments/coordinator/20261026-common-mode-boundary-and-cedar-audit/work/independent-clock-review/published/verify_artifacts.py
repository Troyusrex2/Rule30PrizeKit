"""Audit exact bytes and recorded proof scope, not a replacement for replay."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess

p=argparse.ArgumentParser();p.add_argument('--staged',action='store_true');args=p.parse_args()
root=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=root,text=True).strip())
prefix=root.relative_to(repo).as_posix()
def read(n):return subprocess.check_output(['git','show',':'+prefix+'/'+n],cwd=repo) if args.staged else (root/n).read_bytes()
def data(n):return json.loads(read(n))
def sha(raw):return hashlib.sha256(raw).hexdigest()
files=data('artifacts.json')['files']
for name,digest in files.items():assert sha(read(name))==digest,name
s=data('summary.json')
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert s['official_pin']==pin and s['checker_sha256']==checker
assert sha(subprocess.check_output(['git','show',pin+':Check.lean'],cwd=repo))==checker
expected={'Rule30PeriodicOrPeriodResearch':5,'Rule30PeriodicOrPairCertificate':138,'Rule30TwoPlateauClockResearch':54}
assert s['modules']==expected and s['fully_replayed_constants']==197
for module,count in expected.items():
    src=read('work/'+module+'.lean');r=data('work/formal/'+module+'/report.json')
    assert r['passed'] and r['source_sha256']==sha(src)
    assert r['pin']==pin and r['checker_sha256']==checker
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',src,re.M)
    c=r['checker'];assert c['module']==module and c['verdict']=='pass' and not c['newAxioms']
    assert c['replay']=={'constants':count,'ok':True}
    assert c['claim']=='partial' and c['importsStatements'] and not c['verifiedTargets']
    assert c['headlines'] and all(x['ok'] and x['typeMatches'] for x in c['headlines'])
for dep in data('provenance.json')['dependencies']:
    src=read('work/dependencies/'+dep['module']+'.lean')
    assert sha(src)==dep['sha256'] and src==(repo/dep['source']).read_bytes()
for name in files:
    if name.startswith('work/evidence/') and name.endswith('.guard.json'):
        g=data(name);assert g['exit_code']==0 and g['guard_stop'] is None,name
        assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
        assert g['elapsed_seconds']<=300 and g['peak_owned_rss_bytes']<=8*1024**3
        assert g['minimum_system_available_bytes']>=2*1024**3
cert=data('work/periodic-or-certificate.json')
assert cert['level_counts']==[640,192,112,90]
assert cert['projection_count']==20 and cert['projected_even_reach_pairs']==438
assert cert['all_projected_swaps_excluded'] and cert['literal_row_edges_audited']==256
control=data('work/finite-clock-controls.json')
assert control['passed'] and sum(x['all_words'] for x in control['reports'])==8064
assert sum(x['premise_instances_checked'] for x in control['reports'])==514
odd=control['odd_half_clock_counterexample']
assert (odd['width'],odd['seed'],odd['j'],odd['R'])==(7,20,0,1)
assert odd['older_periodic'] and odd['OR_periodic']
rows=odd['orbit'];width=odd['width'];j=odd['j'];R=odd['R']
for t,x in enumerate(rows):
    y=rows[(t+1)%len(rows)]
    for i in range(width):
        neighborhood=4*((x>>i)&1)+2*((x>>(i-1))&1 if i else 0)+((x>>(i-2))&1 if i>=2 else 0)
        assert ((y>>i)&1)==((30>>neighborhood)&1)
    z=rows[(t+R)%len(rows)]
    assert ((x^z)>>(j+3))&1 and not ((x^z)>>(j+2))&1
    assert bool(x&(3<<(j+4)))==bool(z&(3<<(j+4)))
assert s['arbitrary_even_source_half_clock'] and s['arbitrary_finite_transient_corollary']
for name in ['physical_center_bridge_proved','safety_completeness_proved','full_problem_solved',
             'new_prize_submission','new_pull_request','Wolfram_backend_verification_claimed']:
    assert not s[name]
count=archives=0
for manifest in root.parent.glob('*/artifacts.json'):
    if manifest.parent.name in {root.name,'20261024-seven','20261025-round2','20261025-round2-review'}:continue
    old=json.loads(manifest.read_bytes())['files']
    for name,digest in old.items():assert sha((manifest.parent/name).read_bytes())==digest,(manifest.parent.name,name)
    count+=len(old);archives+=1
assert (count,archives)==(3277,39)
for name in files:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(name),re.I),name
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(files),
                  'fully_replayed_constants':197,'prior_hashes_unchanged':count,
                  'prior_archives_unchanged':archives,'full_problem_solved':False}))
