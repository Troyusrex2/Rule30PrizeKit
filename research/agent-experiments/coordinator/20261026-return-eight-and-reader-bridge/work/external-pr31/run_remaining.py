"""Sequential orchestration; every compiler runs inside its own unchanged resource limits."""
from pathlib import Path
import json,subprocess,sys
root=Path(__file__).resolve().parent
plan=json.loads((root/'split-plan.json').read_bytes());done=[]
out=root/'evidence/remaining-orchestration.log'
with out.open('w',encoding='utf-8') as log:
    for key in plan:
        receipt=root/'official-split'/(key+'.json')
        if receipt.exists():
            assert json.loads(receipt.read_bytes())['passed']
            done.append(key);continue
        proc=subprocess.run([sys.executable,'-B',str(root/'guard_split.py'),'build_dependency.py',key],cwd=root,stdout=log,stderr=subprocess.STDOUT)
        log.flush()
        if proc.returncode:
            print(json.dumps({'passed':False,'failed_key':key,'completed':done}));raise SystemExit(proc.returncode)
        done.append(key);print(key+': guarded compile passed.',flush=True)
(root/'split-completion.json').write_text(json.dumps({'passed':True,'completed':done},indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed':True,'completed_count':len(done)}))
