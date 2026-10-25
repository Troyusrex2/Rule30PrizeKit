"""Validate the complete catalog umbrella after the three fresh module replays."""
import hashlib,json
from core import HERE
from verify_reviewed_front_catalog import PROJECT,LAKE,measured

out=HERE/'front-tools-reviewed-evidence';result=json.loads((out/'report.json').read_text(encoding='utf-8'))
assert result['verdict']=='pass'
info=measured([str(LAKE),'build','Ruliology'],PROJECT,out/'Ruliology.build.log')
record={'verdict':'pass','target':'Ruliology','build':info,
        'umbrella_source_sha256':hashlib.sha256((PROJECT/'lean/Ruliology.lean').read_bytes()).hexdigest(),
        'full_problem_solved':False}
(out/'umbrella-build.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
print({'target':'Ruliology','verdict':'pass','seconds':info['seconds']},flush=True)
