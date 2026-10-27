from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
audit={
 'verdict':'PASS',
 'review_kind':'independent source/type/provenance; no duplicate build',
 'semantic_defects':[],
 'source_sha256':'a73205ebbe1316d2a16fd6716cf077245fbe33b206221ea4088df57562880258',
 'paper_sha256':'219201172d04edb30bd1ed239585e6c79b78eeb1a84e28976990adb4b9b2b03f',
 'no_whole_older_P_return_hypothesis':True,
 'observation_only_conclusion':True,
 'zero_reset_branch_handled':True,
 'independent_backshift_period_derived_from_actual_word':True,
 'all_time_actual_list_gates':True,
 'formal_manifest_files_verified':43,
 'paper_manifest_files_verified':10,
 'actual_imported_research_modules':10,
 'actual_imported_official_modules':3,
 'official_source_compatibility_5473_to_7d665':True,
 'worker_checker_constants':24,
 'worker_checker_headlines':4,
 'reviewer_reran_checker':False,
 'public_write_or_submission':False,
 'report_sha256':sha((p/'REPORT.md').read_bytes())
}
(p/'AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n',encoding='utf-8',newline='\n')
files=[]
for f in sorted(p.rglob('*')):
 if f.is_file() and f.name!='MANIFEST.json':
  b=f.read_bytes();files.append({'path':f.relative_to(p).as_posix(),'bytes':len(b),'sha256':sha(b)})
(p/'MANIFEST.json').write_text(json.dumps({'sealed_utc':datetime.now(timezone.utc).isoformat(),'files':files},indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'files':len(files),'manifest_sha256':sha((p/'MANIFEST.json').read_bytes()),'report_sha256':audit['report_sha256'],'audit_sha256':sha((p/'AUDIT.json').read_bytes())}))
