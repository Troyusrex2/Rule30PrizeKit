"""Check the new fixed-column proposal and its controls in isolated copies."""
from pathlib import Path
import json,subprocess,sys,time
root=Path(__file__).resolve().parent
src=root/'runs/r30-coinailyzer-swarm-20261025T124556Z-e3f1cc5e-v01/src'
results=[]
for name in ['defect_identities','permutive_barrier_scan','frame_retraction','rate_calibration']:
    started=time.monotonic()
    r=subprocess.run([sys.executable,'-B',name+'.py'],cwd=src,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
    (root/('moving-'+name+'.stdout.log')).write_bytes(r.stdout)
    (root/('moving-'+name+'.stderr.log')).write_bytes(r.stderr)
    results.append({'script':name,'exit_code':r.returncode,'seconds':time.monotonic()-started})
    print(json.dumps(results[-1]),flush=True)
(root/'moving-edge-reproduction.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
