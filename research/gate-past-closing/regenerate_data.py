"""Regenerate every numerical triangle/leaf/bridge block in the checked sources.
Standard library only. This is additional reproducibility, not a proof premise.
"""
from pathlib import Path
import ast,json,re,hashlib
ROOT=Path(__file__).resolve().parent
S={8,9,16,18,33,36,66,72,132,144}
SRC=ROOT/'lean-certificate/sources/Ruliology/CellularAutomata'

def columns(gate,size):
    trace=sum((1 if t%2 else 1-((gate>>(t//2))&1))<<t for t in range(size))
    out=[0,trace]
    for j in range(2,size+1):out.append(((out[-1]>>1)^(out[-1]|out[-2]))&((1<<(size+1-j))-1))
    return out

certs={n:json.loads((ROOT/f'certificates/n{n}-CERTIFICATE.json').read_text()) for n in (4,5,6,7)}
expected={(n,v['future_length'],v['future_word']):v for n,d in certs.items() for v in d['terminal_leaves']}
seen=set();leaf_count=0
for file,initial in [(SRC/'Rule30GatePastCover.lean',4),(SRC/'Rule30Certificates/GatePastCases.lean',None)]:
    n=initial
    for line in file.read_text(encoding='utf-8').splitlines():
        if line in ('namespace Five','namespace Six','namespace Seven'):n={'Five':5,'Six':6,'Seven':7}[line.split()[1]]
        if not line.startswith('def leaf'):continue
        match=re.fullmatch(r'def leaf\d+ : Leaf := ⟨(\d+),(\d+),(\d+),(\d+),(\[.*\])⟩',line)
        assert match,line[:100]
        m,f,edge,ref=map(int,match.groups()[:4]);tables=ast.literal_eval(match.group(5));key=(n,m,f)
        c=expected[key];assert edge==max(1,c['sync_column']-1)
        actual=[]
        for p in range(1<<n):
            gate=p|(f<<n)
            actual.append(columns(gate,2*(n+m)) if all(((gate>>i)&255) in S for i in range(n)) else [])
        assert actual==tables and ref==next(p for p,row in enumerate(actual) if row)
        assert key not in seen;seen.add(key);leaf_count+=1
assert seen==set(expected)

text=(SRC/'Rule30PastStrip.lean').read_text(encoding='utf-8')
F=654331177868800777882986221700
for tag,p in [('A',132),('B',528)]:
    m=re.search(r'def triangle'+tag+r' : Triangle := ⟨202,(\[.*\])⟩',text)
    assert m and ast.literal_eval(m.group(1))==columns(p|(F<<10),201)

b=json.loads((ROOT/'BRIDGES.json').read_text());assert b['length']==40 and len(b['paths'])==100
text=(SRC/'Rule30GateTailReduction.lean').read_text(encoding='utf-8')
m=re.search(r'def paths : List \(List Nat\) := (\[.*\])',text)
assert m and ast.literal_eval(m.group(1))==b['paths']
for i,path in enumerate(b['paths']):
    assert len(path)==41 and path[0]==sorted(S)[i//10] and path[-1]==sorted(S)[i%10]
    assert all(v in S for v in path) and all((a>>1)==(c&127) for a,c in zip(path,path[1:]))
print(json.dumps({'leaf_tables_regenerated':leaf_count,'rate_counterexample_triangles_regenerated':2,'bridge_paths_checked':100,'source_bytes_unchanged':True}))
