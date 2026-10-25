"""Test whether source geometry alone explains the N=U phenomenon.

Keep A equal to canonical time U; replace B by a smaller finite configuration.
An equal finite trace is an exact obstruction to any N=U certificate, although
it is not an infinite trace counterexample and B is generally noncanonical.
"""
from pathlib import Path
import json,time
from common_certificate import certify
root=Path(__file__).resolve().parent;tick=time.monotonic()

def step(state):
    if not state:return set()
    return {p for p in range(min(state)-1,max(state)+2)
            if ((p-1 in state) != ((p in state) or (p+1 in state)))}

def trace(state,N):
    out=[]
    for _ in range(N+1):out.append(int(0 in state));state=step(state)
    return out

seed={0};history=[seed]
for _ in range(40):history.append(step(history[-1]))
record=None;tested=0
for U in range(2,9):
    target=trace(history[U],U)
    radius=U-1
    for pattern in range(1,1<<(2*radius+1)):
        B={i-radius for i in range(2*radius+1) if pattern>>i&1}
        tested+=1
        if trace(B,U)!=target:continue
        pair=[sum(1<<(p+U) for p in state) for state in [history[U],B]]
        assert pair[0]&1 and not pair[1]&1
        cap=4*U+32
        future_a,future_b=trace(history[U],cap),trace(B,cap)
        first=next((t for t,(a,b) in enumerate(zip(future_a,future_b)) if a!=b),None)
        record={'U':U,'source_radius':U,'B_radius':radius,
          'A_cells':sorted(history[U]),'B_cells':sorted(B),
          'B_is_canonical':any(B==h for h in history),
          'matching_trace_through':U,'trace':target,
          'first_actual_center_disagreement':first,
          'capped_future_through':cap,'initial_pair_hex':[hex(x) for x in pair]}
        obstruction=certify(U,0,U,initial_pair=pair)
        assert not obstruction['edge_forced']
        record['sparse_N_equals_U']=obstruction
        if first is not None:
            recovered=certify(U,0,cap,initial_pair=pair)
            record['later_sparse_certificate']=recovered
        break
    if record:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'tested':tested,'seconds':time.monotonic()-tick,'record':record,
     'scope':'A finite matching trace for noncanonical B rules out replacing shared single-seed history by support-radius geometry in an N=U argument. No all-time counterexample.'}
(root/'history-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({**out,'record':{k:v for k,v in record.items() if k not in ('sparse_N_equals_U','later_sparse_certificate')}} if record else out),flush=True)
