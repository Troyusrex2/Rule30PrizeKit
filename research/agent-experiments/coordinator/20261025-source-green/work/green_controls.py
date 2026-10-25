"""Independent exact polynomial controls for the right-edge series bridge."""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent
start=time.monotonic()
def phi(a): return a^((a<<1)|(a<<2))
def lin(a): return a^(a<<2)
def density(a): return a&~(a<<1)
def power(a,n):
    bit=0
    while n:
        if n&1: a ^= a << (2<<bit)
        n>>=1; bit+=1
    return a
rows=[1]
for _ in range(2047):rows.append(phi(rows[-1]))
for a in range(8192):assert phi(a)==lin(a)^(density(a)<<1)
convolutions=0
for n in range(257):
    total=power(1,n)
    for s in range(n):total ^= power(density(rows[s])<<1,n-1-s)
    assert total==rows[n]
    convolutions+=1
records=[]
for e in range(11):
    H=1<<e;n=2*H-1
    a=linear=1;shallow=deep=0
    keep=(1<<(e+2))-1
    for s in range(n):
        src=density(a)<<1
        lo=src&keep;hi=src^lo
        linear=lin(linear);shallow=lin(shallow)^lo;deep=lin(deep)^hi
        a=phi(a)
        assert a==linear^shallow^deep
    c=a>>n&1;sh=shallow>>n&1;de=deep>>n&1
    assert (linear>>n&1)==0 and sh==1 and c==1^de
    records.append({'e':e,'time':n,'shallow_depths_through':e,
                    'center':c,'shallow_parity':sh,'deep_parity':de})
out={'finite_only':True,'new_lean_claim':False,'local_row_controls':8192,
     'full_polynomial_convolutions':convolutions,'dyadic_complete_splits':records,
     'elapsed_seconds':time.monotonic()-start,'all_passed':True}
(root/'green-controls.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
