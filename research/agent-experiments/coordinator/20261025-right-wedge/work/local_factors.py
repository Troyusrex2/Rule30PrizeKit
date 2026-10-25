"""Exact one-cell factor maps and two-layer subset implication controls."""
from pathlib import Path
import itertools,json,time
root=Path(__file__).resolve().parent;started=time.monotonic()
def R(l,c,r):return l^(c|r)
def unpack(s):return ((s>>2)&1,(s>>1)&1,s&1)
def delta(s):a,b,h=unpack(s);return a^b
def good(s,t):return (delta(t)*(s&1))==(delta(s)*(t&1))
def subset(s):return not(s&1) or delta(s)
def update(l,c,r):
    al,bl,hl=unpack(l);ac,bc,hc=unpack(c);ar,br,hr=unpack(r)
    return (R(al,ac,ar)<<2)|(R(bl,bc,br)<<1)|(hl^((1^br)*hc)^((1^ac)*hr))
triples=[(l,c,r,update(l,c,r)) for l,c,r in itertools.product(range(8),repeat=3)
         if good(l,c) and good(c,r)]
factors=[]
for mask in range(256):
    if all(((mask>>out)&1)==R((mask>>l)&1,(mask>>c)&1,(mask>>r)&1)
           for l,c,r,out in triples):
        factors.append({'table_integer':mask,'values_by_Abh_state':[(mask>>i)&1 for i in range(8)],
                        'depends_on_h':any(((mask>>i)&1)!=((mask>>(i^1))&1) for i in range(8))})
states=[s for s in range(8) if subset(s)]
counter=None;checked=0
for row in itertools.product(states,repeat=5):
    if not all(good(a,b) for a,b in zip(row,row[1:])):continue
    nxt=[update(*row[i:i+3]) for i in range(3)]
    if not all(good(a,b) for a,b in zip(nxt,nxt[1:])):continue
    checked+=1
    if not subset(nxt[1]) and counter is None:
        counter={'initial_Abh':[unpack(s) for s in row],
                 'next_Abh':[unpack(s) for s in nxt]}
out={'finite_exhaustive_only':True,'Lean_verified':False,'allowed_local_triples':len(triples),
     'factors':factors,'two_layer_admissible_patterns':checked,
     'subset_propagation_counterexample':counter,'seconds':time.monotonic()-started}
(root/'local-factors.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
