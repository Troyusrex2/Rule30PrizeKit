from pathlib import Path
import subprocess,time,json
ROOT=Path(__file__).resolve().parent
start=time.monotonic()
r=subprocess.run([r'C:/Program Files/Wolfram Research/Wolfram Engine/15.0/wolframscript.exe','-file',str(ROOT/'shifted_integer_control.wl')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=45)
(ROOT/'shifted-integer-wolfram-control.log').write_bytes(r.stdout)
assert r.returncode==0,r.stdout[-2000:]
obj=json.loads(r.stdout.decode('utf-8').strip())
assert obj['centerWord']==[1,0,1,0,0] and obj['centerTriple']==[1,1,1]
assert obj['freshSource']==1 and obj['integerDeterminant']==0
assert obj['smallerCenterWord']==[0,1,0,1,0]
assert obj['smallerParentDeterminant']==-1 and obj['smallerChildDeterminant']==0
assert obj['smallerFreshSource']==1
print('independent_Wolfram_control_passed',obj,'seconds',time.monotonic()-start)
