"""Falsify replacing canonical history by centered support and a short edge prefix."""
from pathlib import Path
import json,time
from common_certificate import certify
root=Path(__file__).resolve().parent;tick=time.monotonic()

def F(a):return (a<<1)^(a|(a>>1))
def prefix(a,origin,N):
    value=0
    for t in range(N+1):value|=((a>>origin)&1)<<t;a=F(a)
    return value
def scalar(state,N):
    out=[]
    for _ in range(N+1):
        out.append(int(0 in state))
        state={p for p in range(min(state)-1,max(state)+2)
               if (p-1 in state)!=((p in state) or (p+1 in state))} if state else set()
    return out

records=[];tested=0
for edge_prefix in [0,4]:
    found=None
    for U in range(2,11):
        origin=4*U+40;A=1<<origin
        for _ in range(U):A=F(A)
        target=prefix(A,origin,U)
        for V in range(1,U):
            canonical=1<<origin
            for _ in range(V):canonical=F(canonical)
            fixed={-V:1,V:1}
            for p in range(-V,min(V+1,-V+edge_prefix)):
                fixed[p]=(canonical>>(origin+p))&1
            free=[p for p in range(-V,V+1) if p not in fixed]
            base=sum(v<<(origin+p) for p,v in fixed.items())
            for pattern in range(1<<len(free)):
                B=base|sum(((pattern>>j)&1)<<(origin+p) for j,p in enumerate(free))
                if B==canonical:continue
                tested+=1
                if prefix(B,origin,U)!=target:continue
                aa={p for p in range(-U,U+1) if A>>(origin+p)&1}
                bb={p for p in range(-V,V+1) if B>>(origin+p)&1}
                ta,tb=scalar(aa,4*U+32),scalar(bb,4*U+32)
                assert ta[:U+1]==tb[:U+1]
                first=next((t for t,(a,b) in enumerate(zip(ta,tb)) if a!=b),None)
                pair=[sum(1<<(p+U) for p in s) for s in [aa,bb]]
                failed=certify(U,V,U,initial_pair=pair);assert not failed['edge_forced']
                later=certify(U,V,4*U+32,initial_pair=pair)
                found={'U':U,'V':V,'canonical_left_prefix_cells':edge_prefix,
                  'A_cells':sorted(aa),'B_cells':sorted(bb),
                  'B_is_canonical':False,'matching_trace_through':U,
                  'trace':ta[:U+1],'first_actual_center_disagreement':first,
                  'N_equals_U_obstruction':failed,'later_sparse_certificate':later}
                break
            if found:break
        if found:break
    assert found is not None
    records.append(found)
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'tested':tested,'seconds':time.monotonic()-tick,'records':records,
     'scope':'These finite trace collisions use noncanonical B even with centered bounding edges and an exact four-cell canonical left prefix. They refute only this weakening of an N=U proof, not P1 or all-time observability.'}
(root/'centered-geometry-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({**out,'records':[{k:v for k,v in r.items() if k not in ('N_equals_U_obstruction','later_sparse_certificate')} for r in records]}),flush=True)
