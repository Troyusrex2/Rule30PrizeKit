"""Independent full-initial-word enumeration of the inverse control cases.

No packed planes, inverse recurrence or certificate producer are imported.
"""
from pathlib import Path
import hashlib,json,time
root=Path(__file__).resolve().parent;tick=time.monotonic()
def step(state):
    if not state:return set()
    result=set()
    for p in range(min(state)-1,max(state)+2):
        if (p-1 in state)!=((p in state) or (p+1 in state)):result.add(p)
    return result
def trace(state,N):
    bits=[]
    for _ in range(N+1):bits.append(int(0 in state));state=step(state)
    return bits
path=root/'inverse-geometry-control.json';data=json.loads(path.read_text(encoding='utf-8'))
largest=max(r['U'] for r in data['records']);history=[{0}]
for _ in range(2*largest+1):history.append(step(history[-1]))
tested=0;verified=0;selected=[]
for record in data['records']:
    U,V,K=[record[k] for k in ['U','V','edge_prefix_cells']]
    target=trace(history[U],U);assert target==record['trace']
    fixed={-V:1,V:1,0:target[0]}
    for p in range(-V,min(V+1,-V+K)):
        bit=int(p in history[V])
        if p in fixed and fixed[p]!=bit:
            fixed=None;break
        fixed[p]=bit
    survivors=[]
    if fixed is not None:
        free=[p for p in range(-V,V+1) if p not in fixed]
        base={p for p,b in fixed.items() if b}
        for pattern in range(1<<len(free)):
            tested+=1
            B=base|{p for j,p in enumerate(free) if pattern>>j&1}
            if trace(B,U)==target:survivors.append(sorted(B))
    assert len(survivors)==record['valid_assignments'],(U,V,K,len(survivors),record['valid_assignments'])
    if record['B_cells'] is not None:assert record['B_cells'] in survivors
    verified+=1
for c in data['collisions']:
    U,V,K=[c[k] for k in ['U','V','edge_prefix_cells']]
    A,B=set(c['A_cells']),set(c['B_cells'])
    assert A==history[U] and B!=history[V]
    assert min(A)==-U and max(A)==U and min(B)==-V and max(B)==V
    assert all((p in B)==(p in history[V]) for p in range(-V,min(V+1,-V+K)))
    cap=4*U+32;a,b=trace(A,cap),trace(B,cap)
    assert a[:U+1]==b[:U+1]
    first=next((t for t,(x,y) in enumerate(zip(a,b)) if x!=y),None)
    assert first==c['first_actual_center_disagreement']
    selected.append({'U':U,'V':V,'edge_prefix':K,'first_actual_disagreement':first})
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'inverse_cases_independently_exhausted':verified,'scalar_initial_words_tested':tested,
     'collisions':selected,'seconds':time.monotonic()-tick,
     'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
     'scope':'Independent full-state exhaustion matches the finite inverse-circuit counts. No all-time trace or prize counterexample.'}
(root/'inverse-independent-verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
