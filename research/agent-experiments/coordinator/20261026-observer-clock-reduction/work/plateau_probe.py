"""Try to falsify an OR inverse beyond the proved clock-extending case.
Periodic temporal bands have free upstream inputs, not a white spatial start.
SAT here cannot refute the canonical observer; it can refute a local lemma.
"""
from pathlib import Path
import json,sys,time
sys.path.insert(0,r'D:\MWB\Rule30\wolfram-local\z3-deps')
import z3
r=Path(__file__).resolve().parent;reports=[];begin=time.monotonic()
for physical in [False,True]:
  for L in [1,2,4,8,16]:
    N=2*L;s=z3.Solver();s.set(timeout=5000,max_memory=512)
    rows=[[[z3.Bool(f'{side}_{j}_{t}') for t in range(N)] for j in range(4 if physical else 2)] for side in range(2)]
    # j0 newest g, j1 older h; j2/3 have period L when included.
    for rr in rows:
      g,h=rr[:2]
      for t in range(N):
        s.add(h[(t+L)%N]==z3.Not(h[t]))
        s.add(z3.Implies(h[t],g[(t+1)%N]==z3.Not(g[t])))
        if physical:
          k,l=rr[2:]
          s.add(k[(t+L)%N]==k[t],l[(t+L)%N]==l[t])
          s.add(g[(t+1)%N]==z3.Xor(g[t],z3.Or(h[t],k[t])))
          s.add(h[(t+1)%N]==z3.Xor(h[t],z3.Or(k[t],l[t])))
    a,b=rows
    for t in range(N):s.add(z3.Or(a[0][t],a[1][t])==z3.Or(b[0][t],b[1][t]))
    s.add(z3.Not(a[0][0]),z3.Not(a[1][0]),z3.Not(b[0][0]),z3.Not(b[1][0]))
    s.add(z3.Or([a[0][t]!=b[0][t] for t in range(N)]))
    status=s.check();rec={'driving_clock':L,'physical_two_level_band':physical,'status':str(status)}
    if status==z3.sat:
      model=s.model();bits=[[[int(z3.is_true(model.eval(x,model_completion=True))) for x in col] for col in rr] for rr in rows]
      a,b=bits
      for rr in bits:
        g,h=rr[:2]
        assert all(h[(t+L)%N]==1-h[t] for t in range(N))
        assert all(not h[t] or g[(t+1)%N]==1-g[t] for t in range(N))
        if physical:
          k,l=rr[2:]
          assert all(k[(t+L)%N]==k[t] and l[(t+L)%N]==l[t] for t in range(N))
          assert all(g[(t+1)%N]==g[t]^(h[t]|k[t]) and h[(t+1)%N]==h[t]^(k[t]|l[t]) for t in range(N))
      assert all((a[0][t]|a[1][t])==(b[0][t]|b[1][t]) for t in range(N))
      assert any(a[0][t]!=b[0][t] for t in range(N))
      rec['counterexample']=bits;rec['independent_literal_audit']=True
    reports.append(rec);print(json.dumps(rec),flush=True)
    if status==z3.sat:break
out={'reports':reports,'seconds':round(time.monotonic()-begin,3),'Lean_verified':False,
     'white_boundary_imposed':False,'canonical_observer_refuted':False,'full_problem_solved':False}
(r/'plateau-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
