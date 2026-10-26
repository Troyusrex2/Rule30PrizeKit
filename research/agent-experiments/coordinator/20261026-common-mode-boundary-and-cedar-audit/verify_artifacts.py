"""Audit exact recorded evidence and scope; this does not run Lean replay."""
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
for name,digest in files.items():
    assert (root/name).resolve().is_relative_to(root)
    assert sha(read(name))==digest,name
pin='5473ffd075f63c9d626e63b8455805d4831b39ca'
checker='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert sha(subprocess.check_output(['git','show',pin+':Check.lean'],cwd=repo))==checker
s=data('summary.json');assert s['official_pin']==pin and s['checker_sha256']==checker

def check(c,module,count):
    assert c['module']==module and c['verdict']=='pass' and not c['newAxioms']
    assert c['replay']=={'constants':count,'ok':True}
    assert c['claim']=='partial' and c['importsStatements'] and not c['verifiedTargets']
    assert c['headlines'] and all(x['ok'] and x['typeMatches'] for x in c['headlines'])

own='Rule30CyclicSubsetObstructionResearch'
expected={own:48,'CedarZeroFront':41,'CedarFiniteInjectivity':7}
for module,count in expected.items():
    src=read('work/'+module+'.lean');r=data('work/formal/'+module+'/report.json')
    assert r['source_sha256']==sha(src)
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',src,re.M)
    check(r['checker'],module,count)
    if module==own:assert r['passed'] and r['pin']==pin and r['checker_sha256']==checker
batch=data('work/formal/cedar-stage2-batch.json')
assert batch['passed'] and batch['pin']==pin and batch['checker_sha256']==checker
assert len(batch['new_modules'])==2
for r in batch['new_modules']:
    assert r==data('work/formal/'+r['module']+'/report.json')
meta=data('work/cedar-stage2-source-manifest.json')
assert meta['official_pin']==pin and meta['all_snapshot_hashes_checked']==177
for item in meta['dependencies']:
    name=item['module']+'.lean';src=read('work/dependencies/'+name)
    assert sha(src)==item['source_sha256']
    old=root.parent/'20261026-two-plateau-and-safety-bridge/work'/name
    assert old.read_bytes()==src,name
for n in files:
    if n.startswith('work/evidence/') and n.endswith('.guard.json'):
        g=data(n);assert g['exit_code']==0 and g['guard_stop'] is None,n
        assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
        assert g['elapsed_seconds']<=300 and g['peak_owned_rss_bytes']<=8*1024**3
        assert g['minimum_system_available_bytes']>=2*1024**3

# Independently sealed peer review evidence uses its own documented guard schema.
for kind,count,hashcount in [('clock',388,90),('cyclic',48,32)]:
    base='work/independent-'+kind+'-review/'
    m=data(base+'REVIEW_MANIFEST.json');entries=m['files']
    entries=[dict(v,path=k) for k,v in entries.items()] if isinstance(entries,dict) else entries
    assert len(entries)==hashcount
    for e in entries:assert sha(read(base+e['path']))==e['sha256'],e['path']
    r=data(base+'reproduction/report.json')
    assert r['passed'] and r['kit_pin']==pin and r['checker_sha256']==checker
    assert r['all_custom_constants']==count and sum(x['constants'] for x in r['modules'])==count
    assert r['no_reference_cache'] and r['no_reference_write'] and r['no_install']
    for item in r['modules']:
        module=item['module'];report=data(base+'reproduction/'+module+'.json')
        assert report['passed'] and report['source_sha256']==item['source_sha256']
        assert report['kit_pin']==pin and report['checker_sha256']==checker
        check(report['check'],module,item['constants'])
        candidates=[n for n in files if n.startswith(base) and n.endswith('/'+module+'.lean')]
        assert candidates and all(sha(read(n))==item['source_sha256'] for n in candidates)
    guards=[n for n in files if n.startswith(base+'guard-evidence/') and 'replay' in n and n.endswith('.json')]
    assert len(guards)==1
    g=data(guards[0]);assert g['finished'] and g['exit_code']==0 and not g['guard_stop']
    assert g['elapsed_seconds']<300 and g['peak_rss_bytes']<2*1024**3
assert data('work/independent-clock-review/graph-audit.json')['passed']
assert data('work/independent-cyclic-review/audit.json')['passed']
assert data('work/independent-cyclic-review/supplied-cones-audit.json')['passed']
intake=data('work/cedar-v02-intake.json');assert intake['passed'] and intake['artifacts_checked']==664
assert intake['adopted_new_Lean_findings']==['F005','F006']

# Literal, independent verification of the finite transient and its fixed tail.
A=[58,5,27,36,63,0,0];B=[23,40,27,36,63,0,0];H=[12,12,36,36,63,63,63]
def bit(x,j):return (x>>j)&1
for t in range(6):
    for j in range(6):
        p=(j-1)%6;q=(j-2)%6;n=(j+1)%6
        for rows in [A,B]:
            assert bit(rows[t+1],j)==((30>>(4*bit(rows[t],j)+2*bit(rows[t],p)+bit(rows[t],q)))&1)
        assert bit(H[t+1],j)==bit(H[t],j)^((1-bit(B[t],q))*bit(H[t],p))^((1-bit(A[t],p))*bit(H[t],q))
        assert bit(A[t]^B[t],j)*bit(H[t],n)==bit(H[t],j)*bit(A[t]^B[t],n)
assert H[0] & ~(A[0]^B[0])==0 and H[2] & ~(A[2]^B[2])!=0
assert A[-1]==A[-2] and B[-1]==B[-2] and H[-1]==H[-2]
assert bit(A[1],0)!=bit(A[0],0)

cone=data('work/common-subset-cone-probe.json')['reports']
assert [x['horizon'] for x in cone]==[1,2,3,4,6,8,12]
for c in cone:
    assert c['status']=='sat' and c['not_an_all_time_counterexample']
    T=c['horizon'];width=c['initial_width'];a,b,h=[c['rows'][k] for k in ['a','b','h']]
    d=[[x^y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
    assert all(not h[0][j] or d[0][j] for j in range(width))
    for t in range(T+1):
        for j in range(2*t,width-1):assert d[t][j]*h[t][j+1]==h[t][j]*d[t][j+1]
        if t==T:continue
        for j in range(2*(t+1),width):
            for rows in [a,b]:assert rows[t+1][j]==((30>>(4*rows[t][j]+2*rows[t][j-1]+rows[t][j-2]))&1)
            assert h[t+1][j]==h[t][j]^((1-b[t][j-2])*h[t][j-1])^((1-a[t][j-1])*h[t][j-2])
    assert h[1][c['target']] and not d[1][c['target']]
balance=data('work/profile-balance-probe.json')['first_black_biased']
assert (balance['width'],balance['seed'],balance['period'],balance['ones'],balance['zero_pairs'])==(10,33,32,18,3)
rows=balance['states'];width=balance['width'];newest=[bit(x,width-1) for x in rows]
assert len(rows)==32 and rows[0]==33 and sum(newest)==18
assert sum(not newest[t] and not newest[(t+1)%32] for t in range(32))==3
for t,x in enumerate(rows):
    for j in range(width):
        v=4*bit(x,j)+2*(bit(x,j-1) if j else 0)+(bit(x,j-2) if j>=2 else 0)
        assert bit(rows[(t+1)%len(rows)],j)==(30>>v)&1
assert s['new_root_modules']=={own:48}
assert s['new_cedar_modules_independently_replayed']=={'CedarZeroFront':41,'CedarFiniteInjectivity':7}
for k in ['cyclic_counterexample_has_white_boundary','white_boundary_subset_preservation_refuted',
          'white_boundary_subset_preservation_proved','safety_completeness_proved',
          'physical_center_bridge_proved','full_problem_solved','new_prize_submission',
          'new_pull_request','new_Wolfram_verification_claim']:
    assert not s[k]
count=archives=0
for manifest in root.parent.glob('*/artifacts.json'):
    if manifest.parent.name in {root.name,'20261024-seven','20261025-round2','20261025-round2-review'}:continue
    old=json.loads(manifest.read_bytes())['files']
    for n,digest in old.items():assert sha((manifest.parent/n).read_bytes())==digest,(manifest.parent.name,n)
    count+=len(old);archives+=1
assert (count,archives)==(3317,40)
for n in files:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(files),
                  'new_fully_replayed_constants':96,'independent_previous_review_constants':388,
                  'independent_cyclic_review_constants':48,'prior_hashes_unchanged':count,
                  'prior_archives_unchanged':archives,'full_problem_solved':False}))
