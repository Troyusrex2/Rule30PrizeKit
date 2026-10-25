"""Stress the density proposal after enforcing all four checked free-word exclusions.
Finite-state cycles have exact temporal-function semantics on paper, not Lean.
Language membership is necessary for actual coupling, not sufficient.
"""
from pathlib import Path
from fractions import Fraction
import hashlib,json,random,time
root=Path(__file__).resolve().parent
forbidden=['00','11111','010110','1011010'];rng=random.Random(30302026)
started=time.monotonic();records=[];best=None

def legal(s):return all(w not in s for w in forbidden)

def cycle(prefix,first,cap=30000):
    m=len(prefix);mu=2*m;width=mu+4;mask=(1<<width)-1
    def f(s):return int(prefix[s]) if s<m else first^((s-m)%2)
    cur=sum((1 if t%2==0 else f(t//2))<<t for t in range(width))
    prev=0;seen={};outputs=[]
    for d in range(cap):
        key=(prev,cur)
        if key in seen:
            start=seen[key];word=outputs[start:];period=len(word);black=sum(word)
            return {'entry_depth':start+1,'period':period,'black':black,'density':str(Fraction(black,period)),
                    'cycle_bits':''.join(map(str,word)),
                    'entry_previous_hex':hex(prev),'entry_current_hex':hex(cur),'states':len(outputs)}
        seen[key]=d;outputs.append(cur&1)
        shifted=(cur>>1)|(((cur>>mu)&1)<<(width-1))
        prev,cur=cur,(shifted^(cur|prev))&mask
    return {'unknown_at_states':len(outputs)}

for m in [16,32,64,96,128]:
    for sample in range(100):
        while True:
            prefix='0'
            while len(prefix)<m:
                choices=[str(b) for b in [0,1] if legal(prefix[-6:]+str(b))]
                if not choices:break
                prefix+=rng.choice(choices)
            tails=[first for first in [0,1] if legal(prefix+''.join(str(first^(j%2)) for j in range(32)))]
            if len(prefix)==m and tails:break
        first=rng.choice(tails);assert legal(prefix+''.join(str(first^(j%2)) for j in range(64)))
        c=cycle(prefix,first)
        rec={'prefix_bits':prefix,'alternating_tail_first_bit':first,'sample':sample,**c}
        records.append(rec)
        if 'period' in c and (best is None or Fraction(c['black'],c['period'])<Fraction(best['black'],best['period'])):
            best=rec;print(json.dumps({'new_minimum':rec}),flush=True)
        if best and best['black']*7<best['period']*2:break
    if best and best['black']*7<best['period']*2:break

# An independent scalar reconstruction of the first32columns for the winner.
prefix=best['prefix_bits'];m=len(prefix);first=best['alternating_tail_first_bit'];width=2*m+4
def bit(t):return 1 if t%2==0 else (int(prefix[t//2]) if t//2<m else first^((t//2-m)%2))
columns=[[0]*(width+40),[bit(t) for t in range(width+40)]]
prev=0;cur=sum(bit(t)<<t for t in range(width));mask=(1<<width)-1
for d in range(1,33):
    assert all((cur>>t)&1==columns[d][t] for t in range(width))
    shifted=(cur>>1)|(((cur>>(2*m))&1)<<(width-1))
    prev,cur=cur,(shifted^(cur|prev))&mask
    p,c=columns[-2:];columns.append([c[t+1]^(c[t]|p[t]) for t in range(len(c)-1)])

out={'finite_state_computation':True,'Lean_verified':False,'rng_seed':30302026,
     'forbidden_words':forbidden,'records':records,'best':best,'seconds':time.monotonic()-started,
     'independent_scalar_columns':32,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'Explicit eventually alternating stream satisfying four necessary language exclusions. This is not proved realizable by an actual finite right half.'}
(root/'language-filtered-cycles.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'completed':len(records),'minimum':best['density'],'seconds':out['seconds']}),flush=True)
