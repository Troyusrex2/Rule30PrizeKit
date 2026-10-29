from pathlib import Path
import subprocess,time,json
ROOT=Path(__file__).resolve().parent
start=time.monotonic()
r=subprocess.run([r'C:/Program Files/Wolfram Research/Wolfram Engine/15.0/wolframscript.exe','-file',str(ROOT/'cohomology_control.wl')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=45)
(ROOT/'cohomology-wolfram-control.log').write_bytes(r.stdout)
print(r.stdout.decode('utf-8',errors='replace')[-5000:])
print('exit',r.returncode,'seconds',time.monotonic()-start)
if r.returncode:raise SystemExit(r.returncode)
records=json.loads(r.stdout.decode('utf-8').strip())
expected=json.loads((ROOT/'cohomology-result.json').read_text(encoding='utf-8'))['records']
for a,b in zip(records,expected):
    assert a['constraintRank']==b['constraint_rank']
    assert a['fluxRank']==b['flux_rank']
    assert a['densityDimension']==b['density_dimension']
(ROOT/'cohomology-control-result.json').write_text(json.dumps({'agreed_widths':[a['width'] for a in records],'seconds':time.monotonic()-start,'engine':'Wolfram Language 15 MatrixRank Modulus 2','scope':'Independent exact finite computation; not Lean'},indent=2)+'\n',encoding='utf-8')
