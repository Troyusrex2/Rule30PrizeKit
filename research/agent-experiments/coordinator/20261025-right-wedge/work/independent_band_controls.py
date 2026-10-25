"""Physical scalar checks of the finite-band model, including an escaping control."""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent;started=time.monotonic()
def F(s):
    if not s:return set()
    return {p for p in range(min(s)-1,max(s)+2)
            if ((p-1 in s) != ((p in s) or (p+1 in s)))}
def D(a,b,h):
    if not h:return set()
    return {p for p in range(min(h)-1,max(h)+2)
            if ((p-1 in h)^((p in h) and p+1 not in b)^((p+1 in h) and p not in a))}
def W(a,b,h):
    delta=a^b
    return any(((p+1 in delta) and p in h) != ((p in delta) and p+1 in h)
               for p in range(min(a|b|h)-1,max(a|b|h)+1))
def orbit(L):
    x=1;mask=(1<<(L+1))-1;rows=[]
    while not rows or x!=1:
        rows.append(x);x=(x^((x<<1)|(x<<2)))&mask
    return rows
canon=[{0}]
for _ in range(128):canon.append(F(canon[-1]))
seed_modes=0;rejected=0;physical_updates=0;cases=0
for L in range(1,6):
    T=len(orbit(L))
    for P in range(1,L+2):
        for V in range(T):
            U=V+P;cases+=1
            positions=[U-j for j in range(L) if (U-j in (canon[U]^canon[V]))]
            for mask in range(1,1<<len(positions)):
                seed_modes+=1;h={p for i,p in enumerate(positions) if mask>>i&1}
                failed=False
                for t in range(64):
                    if W(canon[U+t],canon[V+t],h):failed=True;break
                    h=D(canon[U+t],canon[V+t],h);physical_updates+=1
                    if any(not(U+t+1-L < p <= U+t+1) for p in h):failed=True;break
                assert failed,(L,P,V,mask)
                rejected+=1
# A known noncanonical pair DOES carry an escaping common mode. This checks
# that the band test is not merely rejecting all finite physical inputs.
a={-1,0};b={-1};escape_controls=0
for t in range(65):
    h=a^b
    assert h and all(t-1 <= p <= t for p in h)
    assert not W(a,b,h)
    na,nb=F(a),F(b)
    assert D(a,b,h)==(na^nb)
    assert h==({t} if t%2==0 else {t,t-1})
    a,b=na,nb;escape_controls+=1
out={'pass':True,'computational_controls_only':True,'Lean_proof_premise':False,
     'small_physical_cases':cases,'nonzero_initial_subset_modes':seed_modes,
     'rejected_modes':rejected,'physical_D_updates':physical_updates,
     'known_escaping_noncanonical_timesteps':escape_controls,'seconds':time.monotonic()-started}
(root/'independent-band-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
