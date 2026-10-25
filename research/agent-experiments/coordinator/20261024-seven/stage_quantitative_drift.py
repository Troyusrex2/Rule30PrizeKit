"""Release three fully replayed analytic modules without changing older archives."""
import hashlib,json
from pathlib import Path
from core import HERE,REPO
from verification_context import PIN

def main():
 dest=REPO/'research/agent-experiments/coordinator/20261024-seven';files={};modules=[]
 def put(n,source):
  raw=source.read_bytes();p=dest/n;p.parent.mkdir(parents=True,exist_ok=True)
  if p.exists():assert p.read_bytes()==raw,('Existing release differs',n)
  else:p.write_bytes(raw)
  files[n]=hashlib.sha256(raw).hexdigest()
 for module,evidence,out in [('Rule30GoldenQuantitativeDriftResearch','golden-quantitative-drift-evidence','golden-quantitative-drift-evidence'),('Rule30GoldenScaleChargeResearch','golden-scale-charge-v3-evidence','golden-scale-charge-evidence'),('Rule30SignedReaderGaugeResearch','signed-reader-gauge-evidence','signed-reader-gauge-evidence')]:
  source=HERE/(module+'.lean');r=json.loads((HERE/evidence/'report.json').read_text());c=r['check']
  assert r['kit_commit']==PIN and r['checker_unchanged'] and r['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
  assert c['verdict']=='pass' and c['replay']['ok'] and not c['newAxioms'] and all(h['ok'] for h in c['headlines'])
  put(source.name,source)
  for n in ['report.json','check.log']:put(out+'/'+n,HERE/evidence/n)
  modules.append({'module':module,'constants':c['replay']['constants'],'source_sha256':r['source_sha256'],'headlines':[h['name'] for h in c['headlines']]})
 assert sum(m['constants'] for m in modules)==77
 put('QUANTITATIVE-DRIFT.md',HERE/'QUANTITATIVE-DRIFT.md');put('stage_quantitative_drift.py',Path(__file__))
 result={'kit_commit':PIN,'checker_sha256':r['checker_sha256'],'modules':modules,'owned_kernel_constants':77,'files':files,'scale_charge_premise_proved':False,'CQ01_proved':False,'full_problem_solved':False,'new_wolfram_submission':False}
 raw=(json.dumps(result,indent=2)+'\n').encode();target=dest/'quantitative-drift-artifacts.json'
 if target.exists():assert target.read_bytes()==raw
 else:target.write_bytes(raw)
 (HERE/'quantitative-drift-artifacts.json').write_bytes(raw)
 print({'files':len(files)+1,'kernel_constants':77,'counting_premise_proved':False},flush=True)
if __name__=='__main__':main()
