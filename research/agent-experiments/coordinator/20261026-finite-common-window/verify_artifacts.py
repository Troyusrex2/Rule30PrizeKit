"""Audit recorded proof evidence and exact controls; does not rerun Lean."""
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
for module,count in [('Rule30CommonPastResearch',100),('Rule30FiniteCommonWindowResearch',56)]:
    src=read('work/'+module+'.lean');r=data('work/formal/'+module+'/report.json');c=r['checker']
    assert r['passed'] and r['source_sha256']==sha(src)
    assert r['pin']==pin and r['checker_sha256']==checker
    assert c['module']==module and c['verdict']=='pass' and not c['newAxioms']
    assert c['replay']=={'constants':count,'ok':True}
    assert c['claim']=='partial' and c['importsStatements'] and not c['verifiedTargets']
    assert c['headlines'] and all(x['ok'] and x['typeMatches'] for x in c['headlines'])
    assert not re.search(rb'\b(?:sorry|native_decide|bv_decide)\b|^\s*axiom\b|decide\s*\+native|skipKernel',src,re.M)
dep=root.parent/'20261026-common-mode-boundary-and-cedar-audit/work/independent-clock-review/published/work/dependencies/Rule30CommonPastResearch.lean'
assert dep.read_bytes()==read('work/Rule30CommonPastResearch.lean')
for n in files:
    if n.startswith('work/evidence/') and n.endswith('.guard.json'):
        g=data(n);assert g['exit_code']==0 and g['guard_stop'] is None,n
        assert g['limits']=={'seconds':300,'owned_rss_gib':8,'minimum_system_available_gib':2}
        assert g['elapsed_seconds']<=300 and g['peak_owned_rss_bytes']<=8*1024**3
        assert g['minimum_system_available_bytes']>=2*1024**3
intake=data('work/cedar-intake.json')
assert intake['passed'] and intake['artifacts_checked']==87
assert intake['manifest_sha256']=='40e1989e53bb70b9a863ca55e7bd4f6d2e9a5048648b7d5e646bb02a4b76984f'
for n,d in intake['selected'].items():assert sha(read('work/cedar/'+n))==d,n
cert=data('work/cedar/structural/certificate.json');audit=data('work/cedar/structural/audit.json')
assert cert['graph_closed'] and cert['reachable_states']==364 and cert['edges_checked']==2912
assert not cert['forward_implication_holds'] and not cert['backward_implication_holds']
assert audit['all_transitions_checked']==2912 and audit['closed_graph_verified'] and audit['all_nodes_reachable_verified']
assert audit['white_tail_completed_pairs']==audit['shared_tail_completed_pairs']==['00','01','10','11']
assert audit['shared_tail_completions_checked']==1456 and audit['forward_first_Common_failure_time']==3
assert not audit['all_time_Common_claimed'] and not audit['kernel_checked']

# Recompute literal entire-support histories independently from stored graph code.
def step(a,b,h):return a^((a<<1)|(a<<2)),b^((b<<1)|(b<<2)),h^((~(b<<2))&(h<<1))^((~(a<<1))&(h<<2))
def common(a,b,h):return (((a^b)<<1)&h)==((h<<1)&(a^b))
def subset(a,b,h):return (h&~(a^b))==0
rows=[(25,2,24),(111,14,104),(401,50,392),(1783,222,1688)]
for old,new in zip(rows,rows[1:]):assert step(*old)==new
assert all(common(*r) for r in rows[:3]) and not common(*rows[3])
assert subset(*rows[0]) and not subset(*rows[1])
assert ((rows[1][2]&~(rows[1][0]^rows[1][1]))>>3)&1
d=rows[3][0]^rows[3][1];h=rows[3][2]
assert ((d>>3)&1)*((h>>4)&1)!=((h>>3)&1)*((d>>4)&1)
for inp,outp in [((33,34,24),(231,238,8)),((4,108,8),(28,404,40))]:
    assert step(*inp)==outp and common(*inp) and common(*outp)
    assert subset(*inp)!=subset(*outp)
probe=data('work/two-step-closed-transducer.json')
assert probe['status']=='counterexample' and probe['literal_audit']
assert probe['temporal_depth']==2 and probe['whole_halfline_Common_assumed_only_at']==[0,1,2]
assert not probe['all_time_Common_counterexample']
assert [(r['a'],r['b'],r['h']) for r in probe['rows'][:4]]==rows
assert s['genuine_white_boundary'] and s['Actual_and_Mode_all_time'] and s['initial_subset']
assert s['Common_times_proved']==[0,1,2] and s['subset_failure_time']==1 and s['Common_failure_time']==3
for k in ['all_time_Common_counterexample','all_time_subset_preservation_refuted','safety_completeness_proved',
          'physical_center_bridge_proved','full_problem_solved','new_prize_submission',
          'new_pull_request','new_Wolfram_verification_claim']:
    assert not s[k]
count=archives=0
for manifest in root.parent.glob('*/artifacts.json'):
    if manifest.parent.name in {root.name,'20261024-seven','20261025-round2','20261025-round2-review'}:continue
    old=json.loads(manifest.read_bytes())['files']
    for n,d in old.items():assert sha((manifest.parent/n).read_bytes())==d,(manifest.parent.name,n)
    count+=len(old);archives+=1
assert (count,archives)==(3487,41)
for n in files:
    assert not re.search(rb'(?:password|oauth[_-]?token|verification[_ -]?code)\s*[:=]\s*[^\s]',read(n),re.I),n
print(json.dumps({'passed':True,'staged':args.staged,'selected_hashes':len(files),
                  'new_fully_replayed_constants':56,'dependency_replayed_constants':100,
                  'prior_hashes_unchanged':count,'prior_archives_unchanged':archives,
                  'all_time_Common_counterexample':False,'full_problem_solved':False}))
