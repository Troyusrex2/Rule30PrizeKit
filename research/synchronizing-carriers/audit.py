"""Independent literal truth-table checks; no Lean result inferred from Python."""
from pathlib import Path
import json,re,hashlib,time
ROOT=Path(__file__).resolve().parent;started=time.monotonic()
data=json.loads((ROOT/'DATA.json').read_text());prefix=data['prefix'];words=data['cycle'];assert len(prefix)==40 and len(words)==325
source=ROOT/'canonical-package/sources/Ruliology/CellularAutomata/Rule30PeriodicThreeFive.lean'
if not source.exists():source=ROOT/'replay/sources/Ruliology/CellularAutomata/Rule30PeriodicThreeFive.lean'
text=source.read_text(encoding='utf-8')
for name,ws in [('packedCycle',words),('packedPrefix',prefix)]:
    packed=int(re.search(r'def '+name+r' : Nat := (0x[0-9a-f]+)',text).group(1),16)
    assert packed==sum(w<<(16*i) for i,w in enumerate(ws))
def R(p,k):return (words[k%325]>>(p%16))&1
def full(k,p):return ((prefix[k]>>(p%16))&1) if k<40 else R(p,k+285)
def rule(a,b,c):return (30>>(4*a+2*b+c))&1
reference=transient=maps=0
for p in range(16):
    assert full(0,p)==0 and full(1,p)==((65470>>p)&1)
    for k in range(325):
        assert rule(R(p+15,k+2),R(p+15,k+1),R(p+15,k))==R(p,k+1);reference+=1
    for k in range(40):
        assert rule(full(k+2,p),full(k+1,p),full(k,p))==full(k+1,p+1);transient+=1
    for a0,b0 in [(0,0),(0,1),(1,0),(1,1)]:
        a,b=a0,b0
        for k in range(325):
            choices=[c for c in [0,1] if rule(c,b,a)==R(p,k)]
            assert len(choices)==1;a,b=b,choices[0]
        assert (a,b)==(R(p+15,324),R(p+15,325));maps+=1
for r in range(8):
    gate=lambda i:int((r+i)%8 in (0,3))
    word=sum(gate(i)<<i for i in range(8));assert word in {8,9,16,18,33,36,66,72,132,144}
result={'passed':True,'scope':'independent finite literal controls, not an unbounded proof','reference_cells':reference,'transient_cells':transient,'inverse_block_maps':maps,'legal_gate_windows':8,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'seconds':time.monotonic()-started}
(ROOT/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
