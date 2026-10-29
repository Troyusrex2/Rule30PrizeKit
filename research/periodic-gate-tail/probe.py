from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parent
source=ROOT/'CARRIER-SOURCE.json'
data=json.loads(source.read_text());assert data['transient_spatial_states']==1 and data['spatial_cycle_period']==155
words=[s[1] for s in data['states'][1:]];assert len(words)==155
def step(s,d):
    a,b=s
    return b,d^(a|b)
results=[]
for phase in range(10):
    driver=[(w>>phase)&1 for w in words]
    mapping=[]
    for a,b in [(0,0),(0,1),(1,0),(1,1)]:
        s=(a,b)
        for d in driver:s=step(s,d)
        mapping.append(2*s[0]+s[1])
    images=list(range(4));ranks=[]
    for n in range(4):
        images=[mapping[s] for s in images];ranks.append(len(set(images)))
    # Reference inverse is time phase-1, shifted consistently along this carrier.
    prev=(phase+9)%10
    reference=[(words[154]>>prev)&1,(words[0]>>prev)&1]
    results.append({'phase':phase,'one_block_map':mapping,'ranks_after_1_to_4_blocks':ranks,'reference_end_pair':reference})
out={'carrier_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'period':155,'results':results,'kernel_verified':False}
(ROOT/'SYNC-RESULT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
