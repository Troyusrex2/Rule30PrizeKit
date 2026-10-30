"""Independent literal validation of the post-hoc extremal prefix witnesses."""
import json
from pathlib import Path
from edge_horizon_probe import packed_trace,literal_trace

ROOT=Path(__file__).resolve().parent
data=json.loads((ROOT/'edge-horizon-result.json').read_text(encoding='utf-8'))
controls=[]
for row in data['census']:
    w=row['width']
    a,b=row['max_prefix_seed_pair']
    if a is None:
        continue
    c=w//2-1
    tx,ty=packed_trace(a,c,2*w),packed_trace(b,c,2*w)
    assert tx==literal_trace(a,c,2*w)
    assert ty==literal_trace(b,c,2*w)
    first=next(i for i,(u,v) in enumerate(zip(tx,ty)) if u!=v)
    assert first==row['posthoc_max_unequal_edge_common_prefix_bits']
    assert a.bit_length()!=b.bit_length()
    controls.append(dict(width=w,observer=c,seeds=[a,b],
                         left_edges=[c-a.bit_length()+1,c-b.bit_length()+1],
                         first_disagreement=first,independent_literal_control=True))
out=dict(status='all_extremal_witness_controls_passed',controls=controls,
         scope='Finite post-hoc descriptive witnesses; no asymptotic claim.')
(ROOT/'edge-extremal-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=out['status'],count=len(controls),
                      selected=[r for r in controls if r['width'] in [11,12,18]])))
