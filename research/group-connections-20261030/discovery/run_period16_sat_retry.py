from pathlib import Path
import subprocess,time,json
R=Path(__file__).resolve().parent;t=time.monotonic()
p=subprocess.run(['C:/Program Files/Wolfram Research/Wolfram Engine/15.0/wolframscript.exe','-file',str(R/'period16_sat_retry.wl')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=45)
(R/'period16-sat-retry.log').write_bytes(p.stdout)
s=p.stdout.decode('utf-8',errors='replace');print(s[-3500:]);print('exit',p.returncode,'seconds',round(time.monotonic()-t,3))
if p.returncode:raise SystemExit(p.returncode)
records=json.loads(s)
def step(x,N):
 m=(1<<N)-1
 return x^((((x<<1)|(x>>(N-1)))|((x<<2)|(x>>(N-2))))&m)
for r in records:
 if r['status']=='model':
  N=r['n'];orig=sum(b<<j for j,b in enumerate(r['row']));x=orig
  for k in range(1,r['p']+1):
   x=step(x,N)
   if k==r['p']//2:assert x!=orig
  assert x==orig;r['independent_literal_verified']=True;r['seed']=orig
assert records[0]['status']=='model'
(R/'period16-sat-retry-result.json').write_text(json.dumps({'records':records,'seconds':time.monotonic()-t,'engine':'Wolfram Language15 Boolean SatisfiabilityInstances; finite SAT only'},indent=2)+'\n')
