"""Falsify a half-canonical weakening of the N=U deadline, after publication.

Keep all nonnegative cells of B canonical, reconstruct only negative cells,
and require a canonical four-cell left prefix. This remains finite research.
"""
from pathlib import Path
import json,time
from common_certificate import certify
from verify_common import replay
root=Path(__file__).resolve().parent;tick=time.monotonic()
def F(state):
    return {p for p in range(min(state)-1,max(state)+2)
       if (p-1 in state)!=((p in state) or (p+1 in state))} if state else set()
history=[{0}]
for _ in range(258):history.append(F(history[-1]))
records=[];tested=0;stopped=None
for K in [0,4]:
    found=None
    for U in range(2,129):
        trace=[int(0 in history[U+t]) for t in range(U+1)]
        for V in range(1,U):
            if time.monotonic()-tick>190:stopped='internal_time_budget';break
            if trace[0]!=int(0 in history[V]):continue
            tested+=1
            initial=[int(p in history[V]) for p in range(1,U+1)]
            row=initial[:];right=[]
            for t in range(U):
                right.append(row[0]);row=[(row[i-1] if i else trace[t])^(row[i]|row[i+1]) for i in range(len(row)-1)]
            R,C=right,trace;negative={}
            for depth in range(1,U+1):
                L=[C[t+1]^(C[t]|R[t]) for t in range(len(C)-1)]
                negative[-depth]=L[0];R,C=C,L
            if any(negative[p] for p in range(-U,-V)):continue
            if not negative[-V]:continue
            B={p for p,b in negative.items() if b}|{p for p in history[V] if p>=0}
            if not all((p in B)==(p in history[V]) for p in range(-V,min(V+1,-V+K))):continue
            pair=[sum(1<<(p+U) for p in s) for s in [history[U],B]]
            cert=certify(U,V,U,initial_pair=pair);assert not cert['edge_forced']
            checked=replay(cert);assert checked['actual_all_outputs_zero']
            found={'U':U,'V':V,'edge_prefix':K,'A_cells':sorted(history[U]),'B_cells':sorted(B),
              'nonnegative_B_is_canonical':True,'B_is_fully_canonical':B==history[V],
              'trace':trace,'N_equals_U_obstruction':cert,'independent_control':checked}
            break
        if found or stopped:break
    records.append({'edge_prefix':K,'last_U':U,'last_V':V,'collision':found})
    print(json.dumps({'K':K,'last_U':U,'last_V':V,'found':found is not None,'fully_canonical':found['B_is_fully_canonical'] if found else None,'stop':stopped}),flush=True)
    if stopped:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'tested':tested,'seconds':time.monotonic()-tick,'stop':stopped,'records':records,
     'scope':'Post-publication diagnostic: preserve the complete canonical right initial half and test a finite short deadline. No unbounded conclusion.'}
(root/'canonical-half-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'tested':tested,'seconds':out['seconds'],'stop':stopped}),flush=True)
