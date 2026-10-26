"""Falsify candidate binomial-degree monotonicity; exact periodic profiles."""
from pathlib import Path
import json,time
root=Path(__file__).resolve().parent
def integrate(g,bit,P):
    mask=(1<<P)-1;x=g;s=1
    while s<P:x^=x<<s;s*=2
    return ((x<<1)&mask)^(mask if bit else 0)
def degree(x,P):
    if not x:return -1
    d=0
    while P>1:
        H=P//2;lo=x&((1<<H)-1);hi=x>>H
        if lo^hi:d+=H;x=lo^hi
        else:x=lo
        P=H
    return d
def control():
    count=0
    for m in range(5):
        P=1<<m
        for x in range(1<<P):
            # Scalar Boolean-lattice Moebius transform of the temporal truth table.
            a=[(x>>t)&1 for t in range(P)]
            for j in range(m):
                for t in range(P):
                    if t&(1<<j):a[t]^=a[t^(1<<j)]
            expected=max((i for i,b in enumerate(a) if b),default=-1)
            assert degree(x,P)==expected;count+=1
    return count
start=time.monotonic();controls=control();states={(0,0):0};oldP=1;reports=[]
first_degree_drop=None;first_pair_drop=None;first_period_drop=None
for n in range(1,15):
    P=1<<(n-1);new={}
    for (u,v),word in states.items():
        if n>1:u|=u<<oldP;v|=v<<oldP
        du,dv=degree(u,P),degree(v,P)
        for bit in [0,1]:
            w=integrate(u|v,bit,P);dw=degree(w,P)
            initial=word|(bit<<(n-1))
            ex={'width':n,'initial':initial,'degrees':[du,dv,dw]}
            if dv>du and dv>1 and dw<=dv and first_degree_drop is None:first_degree_drop=ex
            if max(du,dv)>1 and max(dv,dw)<max(du,dv) and first_pair_drop is None:first_pair_drop=ex
            if dv>1 and max(dw,0).bit_length()<dv.bit_length() and first_period_drop is None:first_period_drop=ex
            new.setdefault((v,w),initial)
    states=new;oldP=P
    rec={'width':n,'states':len(states),'maximum_degree':max(degree(v,P) for _,v in states)}
    reports.append(rec);print(json.dumps(rec),flush=True)
out={'controls':controls,'reports':reports,'strict_degree_growth_counterexample':first_degree_drop,
     'pair_degree_decrease_counterexample':first_pair_drop,'period_decrease_counterexample':first_period_drop,
     'seconds':round(time.monotonic()-start,3),'finite_only':True,'Lean_verified':False,'full_problem_solved':False}
(root/'complexity-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
