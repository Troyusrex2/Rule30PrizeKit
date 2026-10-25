"""Serialize the already tested N=U derivations; do not expand the census."""
from pathlib import Path
import hashlib,json,time
from common_certificate import certify
root=Path(__file__).resolve().parent;tick=time.monotonic()
old=json.loads((root/'deadline-probe.json').read_text(encoding='utf-8'))
path=root/'deadline-certificates.jsonl'
with path.open('w',encoding='utf-8') as stream:
    for record in old['records']:
        assert time.monotonic()-tick<210
        c=certify(record['U'],record['V'],record['through'])
        assert {k:v for k,v in c.items() if k!='rows'}==record
        stream.write(json.dumps(c,separators=(',',':'))+'\n')
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'matches_prior_cases':True,'certificates':len(old['records']),
     'source_census_not_expanded':True,'seconds':time.monotonic()-tick,
     'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
(root/'deadline-certificate-summary.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
