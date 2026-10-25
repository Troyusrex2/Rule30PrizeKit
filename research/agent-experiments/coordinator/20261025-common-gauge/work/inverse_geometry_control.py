"""Exact bit-sliced left-permutive inversion, for falsifying edge-prefix claims.

Enumerate only the initial right half. A prescribed center trace determines
the left half uniquely. Each integer bit is a separate complete assignment.
No sampling, floating point, or inference beyond the finite caps is used.
"""
from pathlib import Path
import hashlib,json,time
from common_certificate import certify
root=Path(__file__).resolve().parent;tick=time.monotonic()

def step(state):
    return {p for p in range(min(state)-1,max(state)+2)
       if (p-1 in state)!=((p in state) or (p+1 in state))} if state else set()
def scalar_trace(state,N):
    values=[]
    for _ in range(N+1):values.append(int(0 in state));state=step(state)
    return values
history=[{0}]
for _ in range(60):history.append(step(history[-1]))

def solve(U,V,K):
    target=scalar_trace(history[U],U)
    lanes=1<<(V-1);all_ones=(1<<lanes)-1
    initial_right=[]
    for p in range(1,U+1):
        if p==V:plane=all_ones
        elif p>V:plane=0
        else:
            j=p-1
            if j<3:
                byte=[0xaa,0xcc,0xf0][j]
                raw=bytes([byte])*((lanes+7)//8)
            else:
                block=1<<(j-3)
                raw=(bytes(block)+bytes([255])*block)*(lanes//(16*block))
            plane=int.from_bytes(raw,'little')&all_ones
        initial_right.append(plane)
    right=initial_right[:];right_column=[]
    for t in range(U):
        right_column.append(right[0])
        boundary=all_ones if target[t] else 0
        right=[(right[i-1] if i else boundary)^(right[i]|right[i+1])
                for i in range(len(right)-1)]
    C=[all_ones if bit else 0 for bit in target];R=right_column
    negative={}
    for depth in range(1,U+1):
        L=[C[t+1]^(C[t]|R[t]) for t in range(len(C)-1)]
        negative[-depth]=L[0];R,C=C,L
    def value(p):
        if p<0:return negative[p]
        if p==0:return all_ones if target[0] else 0
        return initial_right[p-1]
    valid=all_ones;filter_counts=[]
    constraints=[(p,0,'left_support') for p in range(-U,-V)]
    constraints.append((-V,1,'left_edge'))
    constraints += [(p,int(p in history[V]),'left_prefix')
       for p in range(-V,min(V+1,-V+K))]
    for p,expected,kind in constraints:
        valid &= value(p) if expected else all_ones^value(p)
        filter_counts.append([kind,p,expected,valid.bit_count()])
    # Independently check the entire inversion on each lane when it is small.
    scalar_controls=0
    if lanes<=64:
        for lane in range(lanes):
            state={p for p in range(-U,U+1) if value(p)>>lane&1}
            assert scalar_trace(state,U)==target
            scalar_controls+=1
    count=valid.bit_count();B=None
    if count:
        lane=(valid&-valid).bit_length()-1
        B={p for p in range(-V,V+1) if value(p)>>lane&1}
        assert scalar_trace(B,U)==target
        assert min(B)==-V and max(B)==V and B!=history[V]
        assert all((p in B)==(p in history[V]) for p in range(-V,min(V+1,-V+K)))
    return {'U':U,'V':V,'edge_prefix_cells':K,'right_assignments_exhausted':lanes,
       'valid_assignments':count,'filter_counts':filter_counts,
       'scalar_inversion_controls':scalar_controls,
       'trace':target,'B_cells':sorted(B) if B is not None else None}

records=[];collisions=[];stop=None
for K in [0,4]:
    found=None
    for U in range(2,26):
        for V in range(1,U):
            if time.monotonic()-tick>190:stop='internal_time_budget';break
            r=solve(U,V,K);records.append(r)
            if r['valid_assignments']:
                found=r;break
        if found or stop:break
    if found:
        U,V=found['U'],found['V'];A=history[U];B=set(found['B_cells'])
        pair=[sum(1<<(p+U) for p in s) for s in [A,B]]
        failed=certify(U,V,U,initial_pair=pair);assert not failed['edge_forced']
        cap=4*U+32;ta,tb=scalar_trace(A,cap),scalar_trace(B,cap)
        found={**found,'A_cells':sorted(A),'B_is_canonical':False,
          'first_actual_center_disagreement':next((t for t,(a,b) in enumerate(zip(ta,tb)) if a!=b),None),
          'N_equals_U_obstruction':failed,
          'later_sparse_certificate':certify(U,V,cap,initial_pair=pair)}
        collisions.append(found)
    print(json.dumps({'K':K,'last_U':U,'last_V':V,'collision':{k:v for k,v in found.items() if k not in ('N_equals_U_obstruction','later_sparse_certificate')} if found else None,'stop':stop}),flush=True)
    if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'records':records,'collisions':collisions,'stop':stop,'seconds':time.monotonic()-tick,
     'scope':'Finite inverse-circuit exhaustion. Only actual collisions refute the stated edge-prefix weakening of N=U. No all-time trace or prize counterexample.'}
(root/'inverse-geometry-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'records':len(records),'seconds':out['seconds'],'collisions':len(collisions),'stop':stop}),flush=True)
