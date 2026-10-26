"""Test discounted automaton scores; all discount multipliers are positive."""
from pathlib import Path
from fractions import Fraction
import json,math,sys,time
r=Path(__file__).resolve().parent;d=json.loads((r/'safe-language-machine.json').read_bytes())
sys.path.insert(0,r'D:\MWB\Rule30\toolchain\python-research');import z3
states=d['coupled_states'];edges=d['coupled_edges'];N=d['dfa_states'];targets=d['strict_rank_terminal_states'];reports=[]
for discount in [Fraction(2),Fraction(1,2),Fraction(4),Fraction(1,4)]:
    s=z3.Solver();s.set(timeout=8000,max_memory=1536)
    w=[[z3.Real(f'w{q}_{x}') for x in range(2)] for q in range(N)]
    p=[z3.Real(f'p{i}') for i in range(len(states))]
    rate=z3.RealVal(str(discount.numerator)+'/'+str(discount.denominator));s.add(p[0]==0)
    for i,(q,qn,last,length) in enumerate(states):
        for j,x,y in edges[i]:s.add(w[qn][y]-w[q][x]+p[i]-rate*p[j]>=0)
    for i in targets:s.add(p[i]>=1)
    t=time.monotonic();ans=s.check();out={'discount':str(discount),'status':str(ans),'solver_timeout_ms':8000,'seconds':round(time.monotonic()-t,3)}
    if ans==z3.sat:
        m=s.model()
        def exact(v):
            a=m.eval(v,model_completion=True);return Fraction(a.numerator_as_long(),a.denominator_as_long())
        ww=[[exact(v) for v in row] for row in w];pp=[exact(v) for v in p]
        for i,(q,qn,last,length) in enumerate(states):
            for j,x,y in edges[i]:assert ww[qn][y]-ww[q][x]+pp[i]-discount*pp[j]>=0
        assert pp[0]==0 and all(pp[i]>=1 for i in targets)
        out['exactly_checked']=True;out['weights']=[[str(v) for v in row] for row in ww];out['potential']=[str(v) for v in pp]
    elif ans==z3.unknown:out['reason_unknown']=s.reason_unknown()
    reports.append(out);print(json.dumps({k:v for k,v in out.items() if k not in ['weights','potential']}),flush=True)
(r/'safe-discount-rank.json').write_text(json.dumps({'reports':reports,'uniform_theorem_proved':False,'full_problem_solved':False},indent=2)+'\n')
