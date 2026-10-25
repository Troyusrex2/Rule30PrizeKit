"""Independent scalar cyclic updates and an exact coboundary-space check."""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent;tick=time.monotonic()
d=json.loads((root/'parity-conservation.json').read_bytes())
bases={m:{} for m in range(1,11)};controls=0
def insert(b,row):
    while row:
        i=row.bit_length()-1
        if i in b:row^=b[i]
        else:b[i]=row;return
for L in range(1,d['records'][-1]['ring_length']+1):
    for a in range(1<<L):
        before=[(a>>p)&1 for p in range(L)];after=list(before)
        for _ in range(4):after=[after[(p-1)%L]^(after[p]|after[(p+1)%L]) for p in range(L)]
        for m in range(1,11):
            if len(bases[m])==1<<(m-1):continue
            row=0
            for cells in (before,after):
                for p in range(L):
                    word=sum(cells[(p+j)%L]<<j for j in range(m))
                    row^=1<<word
            insert(bases[m],row)
        controls+=1
for m,basis in bases.items():
    original={int(k):int(v,16) for k,v in d['final_bases'][str(m)].items()}
    assert basis==original and len(basis)==1<<(m-1)
    trivial={};rows=[(1<<(1<<m))-1]
    for node in range(1<<(m-1)):
        rows.append(sum((((v>>1)==node)^((v&((1<<(m-1))-1))==node))<<v for v in range(1<<m)))
    for row in rows:insert(trivial,row)
    assert len(trivial)==1<<(m-1)
    for r in basis.values():
        assert all(((r&q).bit_count()&1)==0 for q in trivial.values())
out={'pass':True,'scalar_ring_states_checked':controls,'window_widths':list(range(1,11)),
     'exact_saved_constraint_bases_match':True,'constant_plus_coboundary_spaces_match':True,
     'arbitrary_width_classification_proved':False,'Lean_verified':False,
     'seconds':time.monotonic()-tick}
(root/'parity-independent-check.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
