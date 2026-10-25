"""Bounded factor-three falsification with the actual driven right dynamics.

This query does not replace the right half by a finite forbidden-word list.
A satisfying model is independently checked; UNSAT is finite and unverified
by Lean, and UNKNOWN is explicitly inconclusive.
"""
import argparse,json,sys,time
from core import BASE,HERE,save
sys.path.insert(0,str(BASE/'toolchain/python-research'))
import z3
from charge_smt import model,controls
from empty_right_absorption import step
from coupled_even_code_probe import decode,even_code,forbidden

def main():
    p=argparse.ArgumentParser();p.add_argument('--length',type=int,default=64)
    p.add_argument('--factor',type=int,default=3);p.add_argument('--timeout-ms',type=int,default=90000)
    p.add_argument('--all-prefixes',action='store_true')
    a=p.parse_args();start=time.monotonic();checked=controls()
    solver,free,evens,_=model(a.length,a.factor,a.timeout_ms)
    if a.all_prefixes:
        constraints=list(solver.assertions())
        assert constraints[-1].decl().kind()==z3.Z3_OP_PB_GE
        solver=z3.Solver();solver.set(timeout=a.timeout_ms,max_memory=1536)
        solver.add(*constraints[:-1])
        solver.add(z3.Or(*[z3.PbGe([(z3.Not(q),1) for q in free[:k]]+
            [(q,-a.factor) for q in evens[:k]],1) for k in range(1,a.length+1)]))
    initial=[z3.Bool(f'right_x_{j}') for j in range(2*a.length)];row=initial
    for t in range(2*a.length-1):
        nxt=[z3.Bool(f'right_r_{t+1}_{j}') for j in range(len(row)-1)]
        for j,v in enumerate(nxt):solver.add(v==z3.Xor(z3.BoolVal(t%2==0) if j==0 else row[j-1],z3.Or(row[j],row[j+1])))
        row=nxt
        if t%2==0:solver.add(free[t//2]==z3.Not(row[0]))
    status=solver.check()
    out={'length':a.length,'factor':a.factor,'timeout_ms':a.timeout_ms,'solver':z3.get_version_string(),
         'solver_status':str(status),'actual_right_dynamics_enforced':True,'controls':checked,
         'every_prefix_checked':a.all_prefixes,
         'Lean_verified':False,'unbounded_charge_proved':False,'full_problem_solved':False}
    if status==z3.sat:
        m=solver.model();f=[int(z3.is_true(m.eval(q))) for q in free]
        E=sum(int(z3.is_true(m.eval(q)))<<j for j,q in enumerate(evens))
        R=sum(int(z3.is_true(m.eval(q)))<<j for j,q in enumerate(initial));x=R;physical=[]
        for t in range(2*a.length-1):
            x=step(x,t)
            if t%2==0:physical.append(1^(x&1))
        assert physical==f and forbidden(f) is None and decode(E,a.length)==f and even_code(f)==E
        violations=[k for k in range(1,a.length+1) if a.factor*(E&((1<<k)-1)).bit_count()<f[:k].count(0)]
        assert violations if a.all_prefixes else a.factor*E.bit_count()<f.count(0)
        out.update({'right_initial_hex':hex(R),'even_input_hex':hex(E),'free_prefix':f,
            'even_black_count':E.bit_count(),'free_zeros':f.count(0),'violating_prefixes':violations,
            'independent_physical_checks_passed':True})
    if status==z3.unknown:out['reason_unknown']=solver.reason_unknown()
    out['seconds']=round(time.monotonic()-start,3)
    save(f'coupled-charge-query-{a.length}-factor{a.factor}'+('-prefixes' if a.all_prefixes else '')+'.json',out)
    print(out,flush=True)

if __name__=='__main__':main()
