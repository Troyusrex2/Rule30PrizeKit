"""Control: translate the already checked AAACBCCC barrier, no graph enlargement."""
from pathlib import Path
import json
R=Path(__file__).resolve().parent
# Actual application order is right to left in the existing positive action.
drive=list(reversed([0,0,0,2,1,2,2,2]))
def low(q):return (q==2,q==1)
def step(v,q):
    c,h=map(int,low(q));return v^(((v<<1)|c)|((v<<2)|(c<<1)|h))
assert all(not low(q)[1] or low(drive[(i+1)%8])[0]!=low(q)[0] for i,q in enumerate(drive))
x,y=42,43;maxbit=0;prefix_return=[];history=[]
for t in range(257):
    maxbit=max(maxbit,(x^y).bit_length()-1)
    if t%16==0:
        assert x&63==42 and y&63==43
        assert (x^y)>>6==0
        prefix_return.append(t)
    history.append((t%8,x&1023,y&1023))
    x,y=step(x,drive[t%8]),step(y,drive[t%8])
first={};cycle=None
for t,s in enumerate(history):
    if s in first:cycle=dict(start=first[s],end=t,period=t-first[s],states=history[first[s]:t]);break
    first[s]=t
out=dict(source_word='AAACBCCC',application_order=drive,initial_pair=[42,43],ticks_checked=256,
    max_difference_digit=maxbit,period16_prefix_and_tail_returns=len(prefix_return),
    lower_ancestor_one_step_constraint=True,finite_projected_cycle=cycle,
    interpretation='Synthetic periodic lower controls, NOT actual black-edge ancestry. Existing exact return-word barrier explains the observed confinement; the 256-tick observation alone is not an all-time proof.')
(R/'ANCESTRY_CONTROL_WITNESS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='finite_projected_cycle'}))
