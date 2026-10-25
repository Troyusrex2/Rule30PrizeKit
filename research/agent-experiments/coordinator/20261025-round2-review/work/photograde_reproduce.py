"""Rerun reviewed supplied computations without changing their sources."""
import json,os,subprocess,sys,time
from pathlib import Path
root=Path(__file__).resolve().parent
source=root/'runs/r30-photograde-20261025T122841Z-abce3ea0-v01/src/coupled_experiments.py'
environment=dict(os.environ,OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2',MKL_NUM_THREADS='2',LOKY_MAX_CPU_COUNT='4',PYTHONDONTWRITEBYTECODE='1')
results={}
for finding in ['F001','F002','F003']:
    started=time.monotonic()
    r=subprocess.run([sys.executable,'-B',str(source),finding],env=environment,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
    (root/(finding+'-photograde.stdout.log')).write_bytes(r.stdout)
    (root/(finding+'-photograde.stderr.log')).write_bytes(r.stderr)
    results[finding]={'seconds':time.monotonic()-started,'results':json.loads(r.stdout)}
    print(json.dumps({'finding':finding,**results[finding]}),flush=True)
(root/'photograde-reproduction.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
