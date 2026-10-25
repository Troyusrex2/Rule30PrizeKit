"""Recheck the actual coarse-patch contradictions with physical cells and Leibniz."""
from pathlib import Path
from itertools import product
import json
from wall_tools import det_leibniz
root=Path(__file__).resolve().parent
data=json.loads((root/'number-wall.json').read_text(encoding='utf-8'))
row={0:1}; bits=[]
for t in range(160):
    bits.append(row.get(0,0))
    row={p:int(bool(row.get(p-1,0)) != bool(row.get(p,0) or row.get(p+1,0)))
         for p in range(-t-1,t+2)}
assert bytes(bits)==(root/'center-65536.bin').read_bytes()[:160]
checks=[]
for name in ['rule30','rule30_source']:
    seq=[v^(name=='rule30_source') for v in bits]
    for key,entry in data['sequences'][name]['coarse_patch_prediction'].items():
        e,f=map(int,key.split(','))
        w=entry['witnesses'][0]
        values=[]
        for value,n,t in [w['old'],w['new']]:
            assert n==2
            patch=[det_leibniz(seq,n+u,t+v) for u,v in product(range(-1,2),repeat=2)]
            assert patch==w['coarse_patch']
            assert det_leibniz(seq,2*n+e,2*t+f)==value
            values.append(value)
        assert values[0] != values[1]
        checks.append({'sequence':name,'fine_parity':key,'equal_patch':w['coarse_patch'],
                       'old':w['old'],'new':w['new'],'independent_check':'physical Rule30 + Leibniz'})
out={'physical_steps':160,'exact_contradictions':checks,'all_passed':True,
     'scope':'Rules from only these nine coarse bits fail; larger alphabets, context, or other tilings are not refuted.'}
(root/'independent-controls.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'physical_steps':160,'contradictions':len(checks),'all_passed':True}))
