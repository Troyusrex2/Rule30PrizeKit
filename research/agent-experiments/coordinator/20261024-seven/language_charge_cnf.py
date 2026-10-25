"""Separate the left counting question from right-word realizability.

Only the proved short word guards are imposed initially. A SAT word is then
queried against actual right dynamics, preventing an approximate-language
counterexample from being mistaken for a coupled counterexample.
"""
import argparse,json,sys,time
from core import HERE,BASE,save
from coupled_charge_cnf import Circuit,solve,CardEnc,EncType
from coupled_even_code_probe import decode,even_code,forbidden
from right_image_smt import make
import z3
from empty_right_absorption import step

def build(n,guard,fixed=None):
    c=Circuit();free=[c.fresh() for _ in range(n)]
    banned=[[0,0],[1]*5,[0,1,0,1,1,0]]
    if guard==7:banned.append([1,0,1,1,0,1,0])
    for word in banned:
        for j in range(n-len(word)+1):c.clauses.append([-free[j+i] if b else free[j+i] for i,b in enumerate(word)])
    if fixed is not None:c.clauses += [[q if b else -q] for q,b in zip(free,fixed)]
    rows=[[-1]*(2*n+1),[1 if t%2==0 else free[t//2] for t in range(2*n)]]
    for d in range(2,2*n+1):rows.append([c.xor(rows[d-1][t+1],c.lor(rows[d-1][t],rows[d-2][t])) for t in range(2*n-d+1)])
    E=[rows[2*d+2][0] for d in range(n)];lits=free[:]
    for e in E:
        lits.append(e)
        for _ in range(2):
            q=c.fresh();c.equal(q,e);lits.append(q)
    enc=CardEnc.atmost(lits,bound=n-1,top_id=c.nv,encoding=EncType.seqcounter)
    c.clauses.extend(enc.clauses);c.nv=enc.nv
    return c,free,E

def validate(n,free,E,m):
    f=[int(q in m) for q in free];e=sum(int(q in m)<<j for j,q in enumerate(E))
    assert forbidden(f) is None and decode(e,n)==f and even_code(f)==e
    assert 3*e.bit_count()<f.count(0)
    return f,e

def main():
    p=argparse.ArgumentParser();p.add_argument('--length',type=int,default=96);p.add_argument('--guard',type=int,choices=[6,7],default=7)
    p.add_argument('--solver',default='g4');p.add_argument('--seconds',type=float,default=90);a=p.parse_args();start=time.monotonic()
    known=json.loads((HERE/'charge-coupled-factor3-image0.json').read_text(encoding='utf-8'))['free_prefix']
    c,f,E=build(len(known),6,known);res,m,_=solve(c,a.solver,8);assert res is True;validate(len(known),f,E,m)
    if any(known[j:j+7]==[1,0,1,1,0,1,0] for j in range(len(known)-6)):
        c,f,E=build(len(known),7,known);assert solve(c,a.solver,8)[0] is False
    c,free,E=build(a.length,a.guard);res,m,stats=solve(c,a.solver,a.seconds)
    out={'length':a.length,'factor':3,'guard':a.guard,'engine':a.solver,'variables':c.nv,'clauses':len(c.clauses),
        'solver_status':'sat' if res is True else 'unsat' if res is False else 'unknown_timeout',
        'actual_right_dynamics_enforced_in_first_query':False,'known_197_bit_control_passed':True,'solver_stats':stats,
        'Lean_verified':False,'unbounded_charge_proved':False,'full_problem_solved':False}
    if res:
        f,e=validate(a.length,free,E,m);out.update({'free_prefix':f,'even_input_hex':hex(e),'free_zeros':f.count(0),'black_even_cells':e.bit_count()})
        for word in [[0,1,0,1,1,0]]+([[1,0,1,1,0,1,0]] if a.guard==7 else []):
            assert all(f[j:j+len(word)]!=word for j in range(len(f)-len(word)+1))
        if a.length<=192:
            solver,initial,cols=make(a.length);solver.set(timeout=5000)
            solver.add(*[q==bool(v) for q,v in zip(cols,f)]);status=solver.check();out['actual_right_realization']=str(status)
            if status==z3.sat:
                mm=solver.model();R=sum(int(z3.is_true(mm.eval(q,model_completion=True)))<<j for j,q in enumerate(initial));x=R;physical=[]
                for t in range(2*a.length-1):
                    x=step(x,t)
                    if t%2==0:physical.append(1^(x&1))
                assert physical==f;out['right_initial_hex']=hex(R);out['independent_right_check_passed']=True
            if status==z3.unknown:out['reason_unknown']=solver.reason_unknown()
    out['seconds']=round(time.monotonic()-start,3)
    save(f'language-charge-cnf-{a.length}-guard{a.guard}-{a.solver}.json',out);print(out,flush=True)

if __name__=='__main__':main()
