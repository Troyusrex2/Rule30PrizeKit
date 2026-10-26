from pathlib import Path
import json,os,sys
if os.environ.get('RULE30_Z3_DEPS'):sys.path.insert(0,os.environ['RULE30_Z3_DEPS'])
import z3
out={'python':sys.version,'z3':z3.get_version_string()}
(Path(__file__).resolve().parent/'runtime-version.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
