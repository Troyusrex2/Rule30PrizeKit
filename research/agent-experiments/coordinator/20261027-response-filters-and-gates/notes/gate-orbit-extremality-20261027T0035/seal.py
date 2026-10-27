from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
prior=['orbit-quotient-20261026T0720/REPORT.md','block-clock-20261026T0625/REPORT.md',
       'ca-canonical-observer-20261026T2314/REPORT.md','even-clock-lifting-20261026T2120/REPORT.md']
result={'status':'paper partial; full gate halving OPEN','new_lean_build':False,'new_kernel_claim':False,
        'new_census':False,'positive_facts':['whole-orbit extremality projects to every actual suffix',
        'clock-birth bits are1 at maximum,0 at minimum'],
        'falsified_candidate':'every nontrivial R-orbit maximum lies outside gated register setG',
        'counterexample':'existing plateau child1736: maxima1782/register6 and1342/register14',
        'actual_target_counterexample':False,'barrier':'gates do not yet transfer to shorter extrema',
        'prior_sources':[{'path':x,'sha256':sha(p.parent/x)} for x in prior]}
(p/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
files=sorted(f for f in p.iterdir() if f.is_file() and not f.name.startswith('MANIFEST'))
manifest={'version':1,'files':[{'path':f.name,'bytes':f.stat().st_size,'sha256':sha(f)} for f in files]}
f=p/'MANIFEST-v1.json';f.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'paper_sha256':sha(p/'PAPER.md'),'manifest_sha256':sha(f),'files':len(files)}))
