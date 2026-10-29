from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
data=json.loads((ROOT/'CARRIER-SOURCE.json').read_text())
w=[s[1] for s in data['states'][1:]]
assert len(w)==155
def R(p,k):return (w[k%155]>>(p%10))&1
out=[]
for p in range(10):
    for k in range(155):
        assert R(p+9,k+2)==(R(p,k+1)^(R(p+9,k+1)|R(p+9,k)))
    images=[]
    for a,b in [(0,0),(0,1),(1,0),(1,1)]:
        for k in range(155):a,b=b,R(p,k)^(a|b)
        assert (a,b)==(R(p+9,154),R(p+9,155))
        images.append([a,b])
    out.append({'phase':p,'images':images,'reference_end_pair':[R(p+9,154),R(p+9,155)]})
(ROOT/'SYNC-AUDIT.json').write_text(json.dumps({'passed':True,'all_phase_reference_recurrences':1550,'all_state_block_maps':40,'results':out,'initial_probe_reference_index_corrected':True,'note':'probe.py compared end positions153,154; correct aligned inverse end positions are154,155. Mapping ranks were unaffected.'},indent=2)+'\n')
(ROOT/'WORDS.json').write_text(json.dumps(w)+'\n')
print(json.dumps({'passed':True,'reference_checks':1550,'block_maps':40,'probe_reference_offset_corrected':True}))
