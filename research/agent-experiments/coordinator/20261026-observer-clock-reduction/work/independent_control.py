from pathlib import Path
import json,time
r=Path(__file__).resolve().parent;start=time.monotonic();reports=[];driver_cases=0
def bits(z,n):return [(z>>i)&1 for i in range(n)]
for P in range(1,8):
  N=2*P;classes={};allowed=0;covered=0;nonunique_masks=0
  for h0 in range(1<<P):
    h=bits(h0,P)*2
    for g0 in range(1<<P):
      for e in [0,1]:
        g=bits(g0,P)+[x^e for x in bits(g0,P)]
        if not all(not h[t] or g[(t+1)%N]==1-g[t] for t in range(N)):continue
        allowed+=1;key=tuple(g[t]|h[t] for t in range(N))
        classes.setdefault(key,[]).append((g,h,e))
  for profile,items in classes.items():
    extending=[i for i in items if i[2] and not all(i[1])]
    if extending:
      covered+=1;g,h,e=extending[0]
      assert all(a==g and b==h and f==1 for a,b,f in items)
      assert all((profile[t]^profile[t+P])==1-h[t] for t in range(P))
    if len(items)>1:nonunique_masks+=1
  for d0 in range(1<<P):
    d=bits(d0,P)
    for initial in range(2):
      g=[initial]
      for t in range(4*P):g.append(g[-1]^d[t%P])
      e=g[P]^g[0]
      assert all(g[t+P]==(g[t]^e) for t in range(3*P+1))
      driver_cases+=1
  reports.append({'clock':P,'all_admissible_pairs':allowed,'or_profiles':len(classes),
                   'clock_extending_unique_profiles':covered,'profiles_with_any_alias':nonunique_masks})
# Dropping the zero-in-mask assumption permits two anti-periodic newer bits.
g=[0,1];g2=[1,0];h=[1,1]
assert all(g[(t+1)%2]==1-g[t] and g2[(t+1)%2]==1-g2[t] for t in range(2))
assert all((g[t]|h[t])==(g2[t]|h[t]) for t in range(2)) and g!=g2
plateau=json.loads((r/'plateau-probe.json').read_bytes())
case=next(x for x in plateau['reports'] if x['physical_two_level_band'] and x['status']=='sat')
a,b=case['counterexample'];P=case['driving_clock'];N=2*P
for rr in [a,b]:
    g,h,k,l=rr
    assert all(h[(t+P)%N]==1-h[t] and k[(t+P)%N]==k[t] and l[(t+P)%N]==l[t] for t in range(N))
    assert all(g[(t+1)%N]==(30>>(4*g[t]+2*h[t]+k[t]))&1 for t in range(N))
    assert all(h[(t+1)%N]==(30>>(4*h[t]+2*k[t]+l[t]))&1 for t in range(N))
assert all((a[0][t]|a[1][t])==(b[0][t]|b[1][t]) for t in range(N))
assert any(a[0][t]!=b[0][t] for t in range(N))
out={'passed':True,'all_clocks_tested':reports,'periodic_driver_cases':driver_cases,
     'zero_assumption_negative_control_passed':True,'plateau_literal_truth_table_passed':True,
     'plateau_has_no_white_ancestry_certificate':True,'seconds':round(time.monotonic()-start,3),
     'Lean_verified':False,'full_problem_solved':False}
(r/'independent-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
