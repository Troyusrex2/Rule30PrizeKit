"""Test whether proved right-exterior coherence suffices for finite lifting.

Finite evidence only. It is not an all-time lifting proof or counterexample.
"""
from pathlib import Path
import json,time
from backward_fields import Canonical,mode_space,image_of_kernel,kernel,contains
root=Path(__file__).resolve().parent;started=time.monotonic()
def phase(fields,history,U,V,N):
    lam=fields[0][U]
    return [fields[t].get(p,0) ^ (lam if history.bit(U+t,p) else 0)
            for t in range(N+1) for p in range(V+t+1,U+t+1)]
records=[];history=Canonical(2*24+4)
for U in range(2,25):
    for V in range(1,U):
        cp=[p for p in range(-U,U+1) if history.bit(U,p)^history.bit(V,p)]
        pp=list(range(-U+1,U));H=U
        cf,cw=mode_space(history,U,V,H,cp)
        pf,pw=mode_space(history,U-1,V-1,H+1,pp)
        white=[pf[1].get(p,0) for p in range(-U,U+1) if p not in cp]
        subset=[1<<i for i,p in enumerate(pp) if not(history.bit(U-1,p)^history.bit(V-1,p))]
        first_cover=None
        snapshots=[]
        for N in range(H+1):
            cr=[r for layer in cw[:N+1] for r in layer]+phase(cf,history,U,V,N)
            basis=kernel(cr,len(cp))
            pr=white+subset+[r for layer in pw[:N+2] for r in layer]+phase(pf,history,U-1,V-1,N+1)
            image,_=image_of_kernel(pr,len(pp),pf[1],cp)
            witness=next((v for v in basis if not contains(image,v)),None)
            if witness is None and first_cover is None:first_cover=N
            if N in {0,1,2,H}:
                rec={'N':N,'dimension':len(basis),'covered':witness is None}
                if witness is not None:
                    # Add the actual difference if needed to retain the left edge.
                    actual=(1<<len(cp))-1
                    if not (witness&1):witness^=actual
                    assert witness&1 and all((r&witness).bit_count()%2==0 for r in cr)
                    assert not contains(image,witness)
                    rec['left_edge_carrying_witness']=[p for i,p in enumerate(cp) if witness>>i&1]
                snapshots.append(rec)
        records.append({'U':U,'V':V,'first_cover_through_U':first_cover,'snapshots':snapshots})
out={'finite_experiment_only':True,'Lean_verified':False,'all_time_lifting_refuted':False,
     'pairs':len(records),'records':records,
     'uncleared_through_U':sum(r['first_cover_through_U'] is None for r in records),
     'max_first_cover':max(r['first_cover_through_U'] for r in records if r['first_cover_through_U'] is not None),
     'seconds':time.monotonic()-started}
(root/'exterior-lift-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='records'}))
print(json.dumps(next((r for r in records if any(not s['covered'] for s in r['snapshots'] if s['N']==2)),None)))
