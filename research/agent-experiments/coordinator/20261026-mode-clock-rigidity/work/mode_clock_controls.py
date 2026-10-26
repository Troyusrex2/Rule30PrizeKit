from pathlib import Path
import itertools,json
r=Path(__file__).resolve().parent
gates=0
for q,k,l,lr,v in itertools.product(range(2),repeat=5):
    eq=((q^v) or (not (k^1) and not lr))==(q or (not k and not l))
    if eq and v:
        assert q==k and (k or not l);gates+=1
local=0
for q0,q1,q2,k0,k1,k2,l0,l1,m0,m1,n0 in itertools.product(range(2),repeat=11):
    if not (q0==k0 and q2==k2 and (k0 or not l0)):continue
    if not (q1==(q0^(1-k0)) and q2==(q1^(1-k1))):continue
    if not (k1==(k0^(l0|m0)) and k2==(k1^(l1|m1)) and l1==(l0^(m0|n0))):continue
    assert (not k1 or k0) and k2==k1;local+=1
def properties(q,k,l,m,n,R):
    T=len(q)
    assert all(len(x)==T for x in [k,l,m,n])
    S=[q[t]|((1-k[t])&(1-l[t])) for t in range(T)]
    return {'q_step':all(q[(t+1)%T]==(q[t]^(1-k[t])) for t in range(T)),
            'k_step':all(k[(t+1)%T]==((30>>(4*k[t]+2*l[t]+m[t]))&1) for t in range(T)),
            'l_step':all(l[(t+1)%T]==((30>>(4*l[t]+2*m[t]+n[t]))&1) for t in range(T)),
            'k_anti':all(k[(t+R)%T]==1-k[t] for t in range(T)),
            'S_repeats':all(S[(t+R)%T]==S[t] for t in range(T))}
controls=[]
for name,q,k,l,m,n,R in [
    ('missing_antiperiod',[0],[1],[0],[0],[0],1),
    ('missing_k_recurrence',[1,0,1,1],[0,0,1,1],[0]*4,[0]*4,[0]*4,2),
    ('missing_l_recurrence',[1,0,1,1],[0,0,1,1],[0]*4,[0,1,0,1],[0]*4,2)]:
    p=properties(q,k,l,m,n,R);assert p['S_repeats'] and p['q_step']
    removed={'missing_antiperiod':'k_anti','missing_k_recurrence':'k_step','missing_l_recurrence':'l_step'}[name]
    assert not p[removed] and all(v for key,v in p.items() if key!=removed)
    controls.append({'name':name,'properties':p})
probe=json.loads((r/'mode-unrestricted-mask-probe.json').read_bytes())
assert all(x['counterexample'] is None for x in probe['reports'])
out={'passed':True,'free_mask_gate_satisfying_rows':gates,'two_gate_down_satisfying_rows':local,
     'finite_local_rows_without_mask_period':sum(x['local_rows'] for x in probe['reports']),
     'negative_controls':controls,'uniform_result_from_Lean_not_finite_enumeration':True,
     'full_problem_solved':False}
(r/'mode-clock-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
