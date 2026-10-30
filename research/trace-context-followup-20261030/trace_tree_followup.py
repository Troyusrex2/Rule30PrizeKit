"""Post-hoc check: finite outputs of a prefix permutation need not be finite aliases."""
import json
import re
from pathlib import Path
from edge_horizon_probe import packed_trace, literal_trace

ROOT = Path(__file__).resolve().parent
pairs = [(86,88),(163,143),(170,196),(171,199),(207,163),(214,216)]


def phi(a):
    return a ^ ((a << 1) | (a << 2))


def stripe(a,j):
    return re.fullmatch('0*(1|11)(01)*',''.join(str(a >> i & 1) for i in range(j+1))) is not None


def cuts(a,b,c):
    return [j for j in range(c+1) if not (a >> (j+1) & 1)
            and not (b >> (j+1) & 1) and a >> (j+2) == b >> (j+2)
            and stripe(a,j) and stripe(b,j)]


results = []
for a,b in pairs:
    x,y = a << 1,(b << 1)|1
    tx,ty = packed_trace(x,1,64),packed_trace(y,1,64)
    assert tx == literal_trace(x,1,64)
    assert ty == literal_trace(y,1,64)
    first = next((i for i,(u,v) in enumerate(zip(tx,ty)) if u != v),None)
    results.append(dict(left_inputs=[a,b], packed_full_rows=[x,y],
                        first_center_disagreement=first, last_time_checked=64,
                        stripe_cuts_at_time0=cuts(x,y,1),
                        stripe_cuts_at_time1=cuts(phi(x),phi(y),2),
                        independent_literal_control=True))
out = dict(status='post_hoc_finite_alias_check',results=results,
           conclusion='A finite prefix permutation output is not an infinite trace alias. No different-row infinite alias is established by this test.')
(ROOT/'trace-tree-followup-result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
