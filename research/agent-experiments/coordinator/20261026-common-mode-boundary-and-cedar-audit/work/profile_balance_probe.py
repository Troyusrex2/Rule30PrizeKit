"""Falsify a global profile-balance shortcut, with complete literal orbits."""
from pathlib import Path
import json

root=Path(__file__).resolve().parent
results=[]
first_biased=first_black_biased=None
for width in range(7,17):
    mask=(1<<width)-1;seen=set();orbits=balanced=white_biased=black_biased=0
    examples=[]
    for seed in range(1,1<<width,2):
        if ((seed>>1)&1)!=((seed>>2)&1) or seed in seen:continue
        states=[];x=seed
        while x not in seen:
            seen.add(x);states.append(x)
            x=(x^((x<<1)|(x<<2)))&mask
        assert x==seed
        profile=[(x>>(width-1))&1 for x in states]
        ones=sum(profile);period=len(states)
        zeros00=sum(profile[t]==profile[(t+1)%period]==0 for t in range(period))
        orbits+=1
        if 2*ones==period:balanced+=1
        elif 2*ones<period:white_biased+=1
        else:black_biased+=1
        if 2*ones!=period and (first_biased is None or (2*ones>period and first_black_biased is None)):
            # Independently reconstruct every cell from the literal rule table.
            for t,a in enumerate(states):
                b=states[(t+1)%period]
                for j in range(width):
                    neighborhood=4*((a>>j)&1)+2*((a>>(j-1))&1 if j else 0)+((a>>(j-2))&1 if j>=2 else 0)
                    assert ((b>>j)&1)==((30>>neighborhood)&1)
            witness={'width':width,'seed':seed,'period':period,'ones':ones,'zero_pairs':zeros00,
                     'states':states,'literal_rule_audited':True,'canonical_100_or_111':True}
            if first_biased is None:first_biased=witness
            if 2*ones>period and first_black_biased is None:first_black_biased=witness
    results.append({'width':width,'canonical_states':len(seen),'orbits':orbits,
                    'balanced':balanced,'white_biased':white_biased,'black_biased':black_biased})
    if first_black_biased is not None:break
out={'results':results,'first_biased':first_biased,'first_black_biased':first_black_biased,
     'no_unbounded_conjecture_claimed':True}
(root/'profile-balance-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'results':results,'black_biased_witness':None if first_black_biased is None else {k:v for k,v in first_black_biased.items() if k!='states'}}))
