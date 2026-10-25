"""Probe an isolated right-front pulse at canonical dyadic return times."""
from pathlib import Path
import json,time
from backward_fields import Canonical
root=Path(__file__).resolve().parent
H=64;history=Canonical((1<<12)+H+3);records=[];started=time.monotonic()
for e in range(2,13):
    U=1<<e;V=1
    rho=next(d for d in range(1,2*U+1) if history.bit(U,U-d))
    blackrun=next(d for d in range(2*U) if not history.bit(U-1,U-1-d))
    assert blackrun==rho
    h={U};first_failure=None;first_physical_failure=None;first_center=None
    physical={U}
    for t in range(H+1):
        delta=lambda p:history.bit(U+t,p)^history.bit(V+t,p)
        if first_center is None and 0 in h:first_center=t
        if first_physical_failure is None and h!=physical:first_physical_failure=t
        if first_failure is None:
            for p in range(U-t-1,U+t+1):
                if (delta(p+1)*(p in h))^(delta(p)*((p+1) in h)):
                    first_failure=t;break
        if t==H:break
        h={p for p in range(U-t-1,U+t+2) if
           ((p-1 in h) ^ ((p in h) and not history.bit(V+t,p+1)) ^
            ((p+1 in h) and not history.bit(U+t,p)))}
        physical={p for p in range(U-t-1,U+t+2) if
                  (p-1 in physical) != ((p in physical) or (p+1 in physical))}
    # Unique backward reconstruction from the white right tail. Two leftover
    # bits beyond the white left tail give a period-three nonfinite tail.
    pre={U:0,U+1:0}
    for p in range(U,-U-1,-1):
        pre[p-1]=int(p==U) ^ ((1^history.bit(0,p+1))*pre[p]) ^ \
                 ((1^history.bit(U-1,p))*pre[p+1])
    finite=(pre[-U]==0 and pre[-U-1]==0)
    subset=finite and all(not pre[p] or (history.bit(U-1,p)^history.bit(0,p))
                          for p in range(-U+1,U))
    wedge=finite and all(not(((history.bit(U-1,p+1)^history.bit(0,p+1))*pre[p]) ^
                             ((history.bit(U-1,p)^history.bit(0,p))*pre[p+1]))
                         for p in range(-U+1,U-1))
    lower=min((rho-2)//2,U-2)
    assert first_failure is None or first_failure>lower
    assert not(subset and wedge)
    records.append({'e':e,'U':U,'V':V,'right_black_run_before':blackrun,
                    'white_gap_after':rho-1,'guaranteed_disjoint_cone_horizon':lower,
                    'first_W_failure_through_cap':first_failure,
                    'first_physical_h_failure_through_cap':first_physical_failure,
                    'first_center_hit_through_cap':first_center,
                    'finite_D_preimage_exists':finite,'previous_subset':subset,'previous_W':wedge,
                    'left_tail_preimage_bits':[pre[-U],pre[-U-1]],
                    'current_h_carries_canonical_left_edge':False})
out={'finite_experiment_only':True,'Lean_verified':False,'full_problem_solved':False,
     'cap':H,'records':records,'seconds':time.monotonic()-started}
(root/'dyadic-pulse-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
