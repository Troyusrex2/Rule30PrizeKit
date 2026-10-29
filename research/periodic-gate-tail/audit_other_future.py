from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
meta=json.loads((ROOT/'OTHER-FUTURE.json').read_text());assert meta['complete']
w=json.loads((ROOT/'OTHER-FUTURE-WORDS.json').read_text());P=len(w);assert P==325
def R(p,k):return (w[k%P]>>(p%16))&1
for p in range(16):
    for k in range(P):
        assert ((30>>(4*R(p+15,k+2)+2*R(p+15,k+1)+R(p+15,k)))&1)==R(p,k+1)
    for a,b in [(0,0),(0,1),(1,0),(1,1)]:
        for k in range(P):
            choices=[c for c in [0,1] if ((30>>(4*c+2*b+a))&1)==R(p,k)]
            assert len(choices)==1;a,b=b,choices[0]
        assert (a,b)==(R(p+15,P-1),R(p+15,P))
out={'passed':True,'reference_cells':16*P,'block_maps':64,'spatial_period':P,'temporal_period':16,'transient_spatial_states':39,'kernel_verified':False}
(ROOT/'OTHER-FUTURE-AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
