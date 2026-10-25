"""Enumerate finite right-boundary image words symbolically, not all inputs.

Only a terminal UNSAT makes the finite image census complete. Neither SAT
nor UNSAT is accepted as a Lean theorem. Every returned word has an exact
independent physical witness. No infinite-language growth law is inferred.
"""
import argparse,json,sys,time
from core import BASE,HERE,save
sys.path.insert(0,str(BASE/'toolchain/python-research'))
import z3
from empty_right_absorption import step
from charge_beam_packed import step as diagonal_step
from coupled_even_code_probe import forbidden,decode

def make(n,engine='standard'):
    solver=z3.Tactic('sat').solver() if engine=='sat' else z3.Solver()
    solver.set(timeout=5000,max_memory=1536)
    initial=[z3.Bool(f'x_{j}') for j in range(2*n)];row=initial;out=[]
    for t in range(2*n-1):
        nxt=[z3.Bool(f'r_{t+1}_{j}') for j in range(len(row)-1)]
        driver=z3.BoolVal(t%2==0)
        for j,v in enumerate(nxt):solver.add(v==z3.Xor(driver if j==0 else row[j-1],z3.Or(row[j],row[j+1])))
        row=nxt
        if t%2==0:out.append(z3.Not(row[0]))
    return solver,initial,out

def encode(f):
    R=Rm=u=0
    for d,s in enumerate(f):
        R1,old=diagonal_step(R,Rm,2*d,1);R,Rm=diagonal_step(R1,old,2*d+1,s)
        u|=((R>>(2*d+1))&1)<<d
    return u

def main():
    p=argparse.ArgumentParser();p.add_argument('--length',type=int,default=20)
    p.add_argument('--seconds',type=float,default=210);p.add_argument('--max-words',type=int,default=50000)
    p.add_argument('--engine',choices=['standard','sat'],default='standard')
    a=p.parse_args();start=time.monotonic();solver,initial,cols=make(a.length,a.engine);image={};best=None;last='not_started'
    while len(image)<a.max_words and time.monotonic()-start<a.seconds:
        status=solver.check();last=str(status)
        if status!=z3.sat:break
        m=solver.model();f=[int(z3.is_true(m.eval(q,model_completion=True))) for q in cols]
        u=sum(int(z3.is_true(m.eval(q,model_completion=True)))<<j for j,q in enumerate(initial))
        x=u;physical=[]
        for t in range(2*a.length-1):
            x=step(x,t)
            if t%2==0:physical.append(1^(x&1))
        assert physical==f and forbidden(f) is None
        w=sum(s<<j for j,s in enumerate(f));assert w not in image;image[w]=u
        E=encode(f);score=3*E.bit_count()-f.count(0)
        if best is None or score<best['factor3_deficit']:
            assert decode(E,a.length)==f
            best={'factor3_deficit':score,'free_word_hex':hex(w),'right_initial_hex':hex(u),
                'even_input_hex':hex(E),'free_zeros':f.count(0),'black_even_cells':E.bit_count()}
        solver.add(z3.Or(*[z3.Not(q) if v else q for q,v in zip(cols,f)]))
        if len(image)%256==0:print({'words':len(image),'seconds':round(time.monotonic()-start,3),'best_factor3':best['factor3_deficit']},flush=True)
    complete=last=='unsat'
    out={'length':a.length,'initial_right_bits':2*a.length,'image_word_count':len(image),
        'finite_census_complete':complete,'last_solver_status':last,
        'solver':z3.get_version_string(),'all_returned_words_have_physical_witnesses':True,
        'engine':a.engine,
        'image_witnesses':{str(w):u for w,u in sorted(image.items())},'best_charge_witness':best,
        'Lean_verified':False,'uniform_language_characterized':False,'unbounded_charge_proved':False,
        'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
    if last=='unknown':out['reason_unknown']=solver.reason_unknown()
    if (HERE/f'right-free-language-{a.length}.json').exists() and complete:
        ref=json.loads((HERE/f'right-free-language-{a.length}.json').read_text(encoding='utf-8'))
        assert len(image)==ref['image_words']
        missing={int(s[::-1],2) for s in ref['missing_words_lsb_time_first']}
        assert not missing&image.keys();out['independent_all_input_lanes_agree']=True
    if a.engine!='standard' and (HERE/f'right-image-smt-{a.length}.json').exists() and complete:
        ref=json.loads((HERE/f'right-image-smt-{a.length}.json').read_text(encoding='utf-8'))
        if ref['finite_census_complete']:
            assert set(ref['image_witnesses'])==set(out['image_witnesses'])
            out['independent_solver_engines_agree']=True
    save(f'right-image-smt-{a.length}'+('' if a.engine=='standard' else '-'+a.engine)+'.json',out)
    print({k:v for k,v in out.items() if k!='image_witnesses'},flush=True)

if __name__=='__main__':main()
