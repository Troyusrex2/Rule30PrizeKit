from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
source=p.parent/'global-temporal-marker-20261027T0030/PAPER.md'
result={'status':'independent paper and arithmetic audit PASS','source':str(source),'source_sha256':sha(source),
        'new_lean_build':False,'new_computational_census':False,'kernel_verification_claim':False,
        'checked':['cyclic valuations','actual word16 profiles and minimal8 return','odd-cover failure on both parities',
                   'K=O*d*(1+c) residual','actual appended heads33/66','whole-L versus2L return consequence'],
        'open':'finite-white noncore exclusion of K=0'}
(p/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
files=sorted(f for f in p.iterdir() if f.is_file() and not f.name.startswith('MANIFEST'))
out={'version':1,'files':[{'path':f.name,'bytes':f.stat().st_size,'sha256':sha(f)} for f in files]}
f=p/'MANIFEST-v1.json';f.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'source_sha256':sha(source),'audit_sha256':sha(p/'AUDIT.md'),'manifest_sha256':sha(f)}))
