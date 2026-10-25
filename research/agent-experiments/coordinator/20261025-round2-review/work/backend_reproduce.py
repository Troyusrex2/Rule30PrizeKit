"""Reproduce exact finite ingredients; do not promote the paper bridge to a proof."""
from pathlib import Path
import json,os,subprocess,sys,time
root=Path(__file__).resolve().parent
base=root/'runs/r30-coinailyzer-backend-20261025T122652Z-ef52115e-v01'
src=base/'src';results=[]
jobs=[('f001',['f001_barrier_escape.py']),
      ('conservation30',['f002_conservation.py','1,2,4','9',str(root/'conservation-rule30-m9.json'),'30']),
      ('conservation184',['f002_conservation.py','1,2,4','5',str(root/'conservation-rule184-m5.json'),'184']),
      ('ether-lifetime',['ether_lifetime.py']),
      ('background-reader',['f003_background_reader.py',str(base/'evidence/t1110/T1110.npy'),str(base/'evidence/t1110/pats.json')])]
for label,args in jobs:
    start=time.monotonic()
    r=subprocess.run([sys.executable,'-B',*args],cwd=src,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
    (root/('backend-'+label+'.stdout.log')).write_bytes(r.stdout)
    (root/('backend-'+label+'.stderr.log')).write_bytes(r.stderr)
    results.append({'label':label,'exit_code':r.returncode,'seconds':time.monotonic()-start})
    print(json.dumps(results[-1]),flush=True)
(root/'backend-reproduction.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
