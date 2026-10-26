from pathlib import Path
import subprocess,sys,json,time
r=Path(__file__).resolve().parent;done=[]
for m in json.loads((r/'refresh-modules.json').read_bytes()):
    t=time.monotonic();z=subprocess.run([sys.executable,'-B',str(r/'guard.py'),'replay.py',m],cwd=r)
    done.append({'module':m,'exit_code':z.returncode,'seconds':round(time.monotonic()-t,3)})
    (r/'refresh-progress.json').write_text(json.dumps(done,indent=2)+'\n')
    if z.returncode:raise SystemExit(z.returncode)
print(json.dumps({'passed':True,'modules':len(done),'seconds':sum(x['seconds'] for x in done)}),flush=True)
