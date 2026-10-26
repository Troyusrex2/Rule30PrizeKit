from pathlib import Path
import json,time
r=Path(__file__).resolve().parent;start=time.monotonic();cases=comparisons=0
def scan(P,n,f):
    flip=0
    for t in range(n):
        if f(t)!=f(t+P):return f(t)^flip
        flip^=1
    return flip
for P in range(1,6):
    mask=(1<<P)-1
    for base in range(1<<P):
      g=base|((mask^base)<<P)
      G=lambda t:(g>>(t%(2*P)))&1
      for hp in range(1<<P):
        H=lambda t:(hp>>(t%P))&1
        if hp==mask:continue
        for kp in range(1<<P):
            K=lambda t:(kp>>(t%P))&1
            if not all(G(t+1)==(G(t)^(H(t)|K(t))) for t in range(2*P)):continue
            cases+=1
            R=lambda t:G(t)|H(t)
            for phase in range(2*P):
                first=next(t for t in range(P) if H(t+phase)==0)
                assert all((R(t+phase)==R(t+phase+P))==bool(H(t+phase)) for t in range(P))
                for n in {first+1,P}:
                    assert scan(P,n,lambda t:R(t+phase))==G(phase)
                    comparisons+=1
# Each missing-premise control keeps the other two structural premises.
no_zero=(scan(1,2,lambda t:1)==0 and (lambda t:1-(t%2))(0)==1)
no_anti=(scan(1,1,lambda t:0)!=0) # g=h=k=0, nonempty zero mask
no_mask_period=(scan(1,2,lambda t:1)!=1) # g=1,0,...;h=0,1,...;k=1
assert no_zero and no_anti and no_mask_period
out={'passed':True,'all_periods_tested':list(range(1,6)),'admissible_periodic_driver_cases':cases,
     'phase_and_horizon_comparisons':comparisons,'missing_zero_control':no_zero,
     'missing_anti_control':no_anti,'missing_mask_period_control':no_mask_period,
     'Lean_verified':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
(r/'clock-search-control.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
