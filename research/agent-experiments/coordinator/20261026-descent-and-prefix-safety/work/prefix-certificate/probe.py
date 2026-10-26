from pathlib import Path
import re,json,itertools
root=Path(__file__).resolve().parent
source=root.parent/'short-extension-root-review-20261026T1840/CedarSafetyBridge.lean'
states=[(int(i),int(p),int(r)) for i,p,r in re.findall(r'\| (\d+) => ⟨\d+,ofNat (\d+),ofNat (\d+)⟩',source.read_text(encoding='utf-8'))]
assert len(states)==36
def evolve(p,r,tail,t):
    row=list(tail)
    for s in range(t):
        a=(p>>(s%8))&1;b=(r>>(s%8))&1;out=[]
        for v in row:
            out.append(v^(a|b));b,a=a,v
        row=out
    return tuple(row)
rows=[];fail=[]
for i,p,r in states:
    for n in range(4):
        for tail in itertools.product((0,1),repeat=n):
            ret=evolve(p,r,tail,8)==tail
            traces=[(evolve(p,r,tail,t)[-1] if n else (p>>(t%8))&1) for t in range(65)]
            bad=next((t for t in range(64) if traces[t]==traces[t+1]==0),None)
            row={'state':i,'tail':list(tail),'return8':ret,'bad00':bad}
            rows.append(row)
            if not ret and bad is None:fail.append(row)
out={'cases':len(rows),'return8_cases':sum(x['return8'] for x in rows),'counterexamples':fail,
     'scope':'fixed 36 return8 boundary pairs, suffix length <=3, explicit 64-step control; not a Lean proof', 'rows':rows}
(root/'probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
