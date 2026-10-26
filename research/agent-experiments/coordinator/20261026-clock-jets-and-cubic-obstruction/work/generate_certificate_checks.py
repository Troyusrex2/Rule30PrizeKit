from pathlib import Path
import json
r=Path(__file__).resolve().parent
header='''module
public import Rule30CubicCertificateData
@[expose] public section
namespace MODULE
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
'''
modules=[];heads={}
for part,start in enumerate(range(0,290,32)):
    name=f'Rule30CubicOrbitCheck{part:02d}'
    claim=f'(orbits.drop {start} |>.take {min(32,290-start)}).all checkOrbit=true'
    s=header.replace('MODULE',name)+f'theorem checked : {claim} := by decide +kernel\nend {name}\n'
    (r/(name+'.lean')).write_text(s,encoding='utf-8');modules.append(name);heads[name]=['checked']
for part,start in enumerate(range(0,64,4)):
    name=f'Rule30CubicMomentCheck{part:02d}'
    s=header.replace('MODULE',name)
    for a in range(start,start+4):
        claim=f'(List.range {64-a}).all (fun j => !(moment {a} ({a}+j)))=true'
        s+=f'theorem row{a} : {claim} := by decide +kernel\n'
    s+=f'end {name}\n'
    (r/(name+'.lean')).write_text(s,encoding='utf-8');modules.append(name)
    heads[name]=[f'row{a}' for a in range(start,start+4)]
p=r/'replay.py';t=p.read_text(encoding='utf-8')
for name,h in heads.items():
    line=f'HEADS[{name!r}]={h!r}\n'
    if line not in t:t=t.replace('assert module in HEADS',line+'assert module in HEADS')
p.write_text(t,encoding='utf-8')
(r/'certificate-check-modules.json').write_text(json.dumps(modules,indent=2)+'\n')
print(json.dumps({'modules':len(modules),'orbit_checks':290,'normalized_moments':2080}))
