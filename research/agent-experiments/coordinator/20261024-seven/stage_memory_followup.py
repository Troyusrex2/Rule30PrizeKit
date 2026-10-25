"""Publish an allowlisted continuation, preserving all earlier hashed artifacts."""
import hashlib,json
from pathlib import Path
from core import HERE,REPO
from verification_context import PIN

def main():
 dest=REPO/'research/agent-experiments/coordinator/20261024-seven';bundle=HERE/'g913-offload/results/budget8-complete'
 cm=json.loads((bundle/'collection-manifest.json').read_text(encoding='utf-8'));assert cm['certificate_complete'] and cm['leaves']==404
 files={};modules=[];checker=cm['checker_sha256']
 def put(name,data):
  if isinstance(data,Path):data=data.read_bytes()
  data=data.replace(b'\r\n',b'\n')
  p=dest/name;p.parent.mkdir(parents=True,exist_ok=True)
  if p.exists():assert p.read_bytes()==data,('already-public artifact changed',name)
  else:p.write_bytes(data)
  files[name]=hashlib.sha256(data).hexdigest()
 def checked(module,source,report,source_out=None,report_out=None,kind='mathematical'):
  r=json.loads(report.read_text(encoding='utf-8'));ck=r['check'];raw=source.read_bytes();digest=hashlib.sha256(raw).hexdigest()
  assert digest==r['source_sha256'] and r['kit_commit']==PIN and r['checker_sha256']==checker
  assert ck['verdict']=='pass' and ck['replay']['ok'] and not ck['newAxioms'] and all(h['ok'] for h in ck['headlines'])
  assert b'\r\n' not in raw
  sn=source_out or source.name;rn=report_out or report.relative_to(HERE).as_posix();put(sn,raw);put(rn,report)
  modules.append({'module':module,'source':sn,'source_sha256':digest,'report':rn,'constants':ck['replay']['constants'],'headlines':[h['name'] for h in ck['headlines']],'kind':kind})
 for module,folder in [('Rule30GoldenCompactPathResearch','golden-compact-path-evidence'),('Rule30TotalSpatialChargeReductionResearch','total-spatial-charge-reduction-evidence'),
   ('Rule30BothZeroCountRankObstructionResearch','bothzero-count-obstruction-evidence'),('Rule30ZeroRunSpatialChargeReductionResearch','zero-run-spatial-charge-reduction-evidence'),('Rule30GoldenBudget8CoupledResearch','golden-budget8-coupled-evidence')]:
  checked(module,HERE/(module+'.lean'),HERE/folder/'report.json')
 checked('Rule30GoldenCompactLeafProbeResearch',HERE/'Rule30GoldenCompactLeafProbeResearch.lean',HERE/'g913-offload/results/20261025T033619Z-replay24/report.json',report_out='memory-offload-evidence/probe-replay-report.json',kind='engineering_probe')
 for m,stamp in [('Rule30GoldenCompactJoinSmoke4Research','20261025T035716Z'),('Rule30GoldenBudget8JoinPreflightResearch','20261025T040014Z')]:
  checked(m,HERE/'g913-offload/_cache'/(m+'.lean'),HERE/'g913-offload/results'/(stamp+'-'+m)/'report.json',report_out='memory-offload-evidence/'+m+'/report.json',kind='engineering_preflight')
 for rec in cm['modules']:
  checked(rec['module'],bundle/'formal'/(rec['module']+'.lean'),bundle/rec['report'],source_out='budget8-partition/formal/'+rec['module']+'.lean',report_out='budget8-partition/'+rec['report'])
 for name in ['plan.json','collection-manifest.json','original-batch-manifest.json']:put('budget8-partition/'+name,bundle/name)
 put('budget8-partition/corrected-batch-manifest.json',HERE/'g913-offload/_cache/budget8-c600-v2/batch-manifest.json')
 put('memory-offload-evidence/worker-initial-report.json',HERE/'g913-offload/results/20261025T033057Z/report.json')
 put('memory-offload-evidence/slow-join-report.json',HERE/'g913-offload/results/20261025T035520Z-Rule30GoldenCompactJoinSmoke3Research/report.json')
 put('memory-offload-evidence/Rule30GoldenCompactJoinSmoke3Research.lean',HERE/'g913-offload/_cache/Rule30GoldenCompactJoinSmoke3Research.lean')
 for name in ['budget8-verified-transfer.json','transfer-manifest.json','budget8-transfer.json']:put('memory-offload-evidence/'+name,HERE/'g913-offload/_cache'/name)
 scripts=['nonlocal_stack_rank','actual_coupled_rank','regular_prefix_rank','regular_prefix_rank_terminal','actual_coupled_bothzero_rank',
  'regular_prefix_bothzero_rank_terminal','regular_prefix_bothzero_window_rank_terminal','regular_prefix_bothzero_window_rank_terminal_refined',
  'nonlocal_dyck_features','actual_coupled_bothzero_dyck_rank','actual_coupled_bothzero_dyck_rank_ipm','actual_bothzero_semidefinite_rank',
  'joint_spatial_charge','joint_spatial_charge_cnf','joint_spatial_local_charge','bothzero_linear_obstruction','validate_bothzero_obstruction',
  'plan_golden_budget_partition','receive_budget8','stage_memory_followup','zero_run_spatial_charge','spatial_flux_rank','spatial_flux_rank_valid','spatial_flux_rank_three_columns','validate_spatial_flux']
 for name in scripts:put(name+'.py',HERE/(name+'.py'))
 data=['nonlocal-stack-rank','actual-coupled-rank','regular-prefix-rank','regular-prefix-rank-terminal','actual-coupled-bothzero-rank',
  'regular-prefix-bothzero-rank-terminal','regular-prefix-bothzero-window-rank-terminal','regular-prefix-bothzero-window-rank-terminal-refined',
  'actual-coupled-bothzero-dyck-rank','actual-coupled-bothzero-dyck-rank-ipm','actual-bothzero-semidefinite-rank','actual-bothzero-semidefinite-rank-homogeneous',
  'joint-spatial-charge-c1','joint-spatial-charge-cnf-48-g4','joint-spatial-charge-cnf-96-g4','joint-spatial-local-charge','bothzero-linear-obstruction','bothzero-linear-obstruction-validation','zero-run-spatial-charge','spatial-flux-rank','spatial-flux-rank-valid','spatial-flux-rank-three-columns','spatial-flux-controls']
 for name in data:put(name+'.json',HERE/(name+'.json'))
 for name in ['README.md','REPRODUCE.md','prepare.py','bootstrap.py','worker.py','prepare_budget8.py','prepare_budget8_v2.py','budget8_worker.py','check_one.py','complete_budget8_v2.py','collect_budget8.py','replay_probe.py']:
  put('g913-offload/'+name,HERE/'g913-offload'/name)
 root=next(m for m in modules if m['module']=='Rule30GoldenBudget8C600V2Research');r=json.loads((dest/root['report']).read_text(encoding='utf-8'))
 status=('All **404 leaves and the corrected root passed full kernel replay**. '
  f"The root replay checked {r['check']['replay']['constants']} owned declarations in {r['replay']['seconds']} seconds, "
  f"peaking at {r['replay']['peak_tree_rss_gib']} GiB RSS. "
  '`minimum_nine` proves at least nine black even-code samples among the first 102 for every Golden stream. '
  'The separately checked coupled bridge gives at least nine black cells of `Psi(R)` at depths 2,4,...,204, for arbitrary right halves, including infinite ones.')
 text=(HERE/'MEMORY-AND-NEW-TARGET.md').read_text(encoding='utf-8');assert 'FINAL_CERTIFICATE_STATUS_TO_FILL_FROM_CHECKER' in text
 text=text.replace('FINAL_CERTIFICATE_STATUS_TO_FILL_FROM_CHECKER',status);put('MEMORY-AND-NEW-TARGET.md',text.encode('utf-8'))
 manifest={'kit_commit':PIN,'checker_sha256':checker,'files':files,'modules':modules,'owned_replayed_constants':sum(m['constants'] for m in modules),
  'budget8_full_kernel_certificate_completed':True,'unbounded_charge_proved':False,'CQ01_proved':False,'full_problem_solved':False,
  'new_wolfram_submission':False,'legacy_reports_unchanged':True,'method':'full per-module official kernel replay; every remote source and import object rehashed before collection'}
 raw=(json.dumps(manifest,indent=2)+'\n').encode('utf-8');(HERE/'memory-followup-artifacts.json').write_bytes(raw);put('memory-followup-artifacts.json',raw)
 print({'files':len(files),'modules':len(modules),'owned_constants':manifest['owned_replayed_constants'],'full_problem_solved':False},flush=True)
if __name__=='__main__':main()
