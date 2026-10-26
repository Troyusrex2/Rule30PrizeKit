"""Sequential independent kernel jobs, each with the unchanged resource guard."""
from pathlib import Path
import subprocess,sys,json,time
r=Path(__file__).resolve().parent
modules=json.loads((r/'certificate-check-modules.json').read_bytes())
done=[]
for module in modules:
    start=time.monotonic()
    code=subprocess.call([sys.executable,'-B',str(r/'guard.py'),'replay.py',module],cwd=r)
    done.append({'module':module,'exit_code':code,'seconds':round(time.monotonic()-start,3)})
    (r/'certificate-batch-progress.json').write_text(json.dumps(done,indent=2)+'\n')
    if code:raise SystemExit(code)
print(json.dumps({'all_passed':True,'modules':len(done),'seconds':sum(x['seconds'] for x in done)}),flush=True)
