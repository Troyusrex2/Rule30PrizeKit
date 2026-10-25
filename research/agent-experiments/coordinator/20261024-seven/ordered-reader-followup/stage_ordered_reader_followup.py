"""Stage immutable formal counterexamples and complete neural experiment records."""
import ast,hashlib,json
from pathlib import Path
from core import HERE,REPO
from verification_context import PIN

def sha(raw):return hashlib.sha256(raw).hexdigest()

def main():
 dest=REPO/'research/agent-experiments/coordinator/20261024-seven';prefix='ordered-reader-followup/';files={}
 def put(name,raw):
  if isinstance(raw,Path):raw=raw.read_bytes()
  target=dest/name;target.parent.mkdir(parents=True,exist_ok=True)
  if target.exists():assert target.read_bytes()==raw,('Prior release byte mismatch',name)
  else:target.write_bytes(raw)
  files[name]=sha(raw)
 put(prefix+'.gitattributes',b'* -text whitespace=cr-at-eol,-blank-at-eof\n*.npz binary\n*.pt binary\n')
 put(prefix+'.gitignore',b'!order-reader-data/actual-bothzero-ordered.npz\n!ordered-reader-v2/actual-bothzero-ordered.npz\n!ordered-reader-v2/results/relu-reader-weights.pt\n!ordered-reader-v2/results/gru-reader-weights.pt\n!ordered-reader-v3/actual-bothzero-ordered.npz\n!ordered-reader-v3/results/relu-reader-weights.pt\n!ordered-reader-v3/warmstart/v2-relu-reader-weights.pt\n')
 names=['prepare_order_reader_data','regular_prefix_bothzero_rank_terminal','prefix_monotone_rank_audit','validate_prefix_monotone_rank','zero_run_charge_beam','build_zero_run_charge_counterexample','prepare_ordered_reader_v2','prepare_ordered_reader_v3','validate_ordered_reader_v2','guard_order_reader_v2_remote','guard_order_reader_v3_remote','audit_ordered_reader_v3']
 todo=names[:];seen=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  f=HERE/(n+'.py')
  if not f.is_file():continue
  seen.add(n);put(prefix+f.name,f)
  for node in ast.walk(ast.parse(f.read_text(encoding='utf-8-sig'))):
   if isinstance(node,ast.ImportFrom) and node.module and (HERE/(node.module+'.py')).is_file():todo.append(node.module)
 for n in ['train_ordered_rank_reader.py','guard_order_reader_remote.py','prefix-monotone-rank-audit.json','prefix-monotone-rank-validation.json','zero-run-charge-beam.json','zero-run-charge-counterexample-provenance.json']:
  put(prefix+n,HERE/n)
 for n in ['actual-bothzero-ordered.npz','data-manifest.json','sources.json','README.md']:
  put(prefix+'order-reader-data/'+n,HERE/'order-reader-data'/n)
 for n in ['relu-reader-report.json','guard-report.json']:
  put(prefix+'ordered-reader-baseline-results/'+n,HERE/'ordered-reader-baseline-results'/n)
 for dirname in ['ordered-reader-v2','ordered-reader-v3']:
  root=HERE/dirname;required=['sources.json','OWNER.txt','README.md','data-manifest.json','actual-bothzero-ordered.npz','architecture-controls.json','guard-report.json']
  if dirname.endswith('v2'):required+=['baseline-provenance.json']
  for f in required:assert (root/f).is_file(),(dirname,f)
  for n,h in json.loads((root/'sources.json').read_text()).items():assert sha((root/n).read_bytes())==h,(dirname,n)
  for f in sorted(root.rglob('*')):
   if f.is_file() and not any(x in f.relative_to(root).parts for x in ['_cache','__pycache__']):put(prefix+dirname+'/'+f.relative_to(root).as_posix(),f)
  meta=json.loads((root/'data-manifest.json').read_text());assert sha((root/'actual-bothzero-ordered.npz').read_bytes())==meta['data_sha256']
  for f in sorted((root/'results').glob('*-reader-report.json')):
   r=json.loads(f.read_text());assert r['source_sha256']==sha((root/'train_ordered_rank_reader.py').read_bytes())
   assert r['data_sha256']==meta['data_sha256'] and r['padding_invariance_max_error']==0
   assert not r['uniform_rank_proved'] and not r['full_problem_solved']
   weight=root/'results'/(r['architecture']+'-reader-weights.pt');assert sha(weight.read_bytes())==r['weight_sha256']
   assert not r['float64_training']['nonfinite'] and not r['float64_heldout']['nonfinite']
 modules=[]
 for module,evidence in [('Rule30PrefixMonotoneRankObstructionResearch','prefix-monotone-rank-obstruction-evidence'),('Rule30PrefixMonotoneOrderObstructionResearch','prefix-monotone-order-obstruction-evidence'),('Rule30ZeroRunChargeCounterexampleResearch','zero-run-charge-counterexample-evidence')]:
  source=HERE/(module+'.lean');rp=HERE/evidence/'report.json';r=json.loads(rp.read_text());c=r['check']
  assert r['kit_commit']==PIN and r['checker_unchanged'] and r['source_sha256']==sha(source.read_bytes())
  assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] for h in c['headlines'])
  put(source.name,source)
  for n in ['report.json','check.log']:put(evidence+'/'+n,HERE/evidence/n)
  modules.append({'module':module,'source_sha256':r['source_sha256'],'kernel_constants':c['replay']['constants'],'headlines':[h['name'] for h in c['headlines']]})
 put('ORDERED-READER-FOLLOWUP.md',HERE/'ORDERED-READER-FOLLOWUP.md')
 put(prefix+'stage_ordered_reader_followup.py',Path(__file__))
 manifest={'kit_commit':PIN,'checker_sha256':r['checker_sha256'],'files':files,'modules':modules,'new_kernel_constants':sum(m['kernel_constants'] for m in modules),'prefix_rank_official_evolution_bridge_formalized':False,'zero_run_counterexample_official_Theta_bridge_formalized':True,'neural_experiments_Lean_verified':False,'uniform_rank_proved':False,'No00SpatialCharge_proved':False,'CQ01_proved':False,'full_problem_solved':False,'new_wolfram_submission':False}
 raw=(json.dumps(manifest,indent=2)+'\n').encode();(HERE/'ordered-reader-artifacts.json').write_bytes(raw);put('ordered-reader-artifacts.json',raw)
 print({'files':len(files),'bytes':sum((dest/n).stat().st_size for n in files),'new_kernel_constants':manifest['new_kernel_constants']},flush=True)
if __name__=='__main__':main()
