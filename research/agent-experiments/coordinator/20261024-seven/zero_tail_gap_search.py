"""Search actual Golden prefixes for long zero-even gaps; no unbounded claim.

An exact decoder and scalar re-encoding validate the best witness. In
particular, a finite gap is not called an infinitely supported counterexample.
"""
import argparse,json,random,time
from core import save
from charge_beam_packed import step,controls,check_full
from zero_tail_rank import random_free

def main():
    p=argparse.ArgumentParser();p.add_argument('--prefix',type=int,default=128)
    p.add_argument('--trials',type=int,default=50000);p.add_argument('--seconds',type=float,default=210)
    a=p.parse_args();rng=random.Random(302481);start=time.monotonic();checked=controls();best=None;records=[]
    for trial in range(a.trials):
        f=random_free(a.prefix,rng);R=Rm=u=0
        for d,s in enumerate(f):
            R1,old=step(R,Rm,2*d,1);R,Rm=step(R1,old,2*d+1,s)
            u|=((R>>(2*d+1))&1)<<d
        run=0
        for s in reversed(f):
            if not s:break
            run+=1
        gap=0
        for d in range(a.prefix,a.prefix+256):
            R1,old=step(R,Rm,2*d,1);base,_=step(R1,old,2*d+1,0);s=(base>>(2*d+1))&1
            if (not s and run==0) or (s and run==4):break
            R=base^(((1<<(2*d+2))-1) if s else 0);Rm=R1
            run=run+1 if s else 0;gap+=1;f.append(s)
        if best is None or gap>best['zero_even_gap']:
            best={'trial':trial,'zero_even_gap':gap,'free_prefix':f,'even_input_hex':hex(u),
                'free_prefix_hex':hex(sum(s<<j for j,s in enumerate(f))),
                'length':len(f),'zero_gap_start':a.prefix,'seconds':round(time.monotonic()-start,3)}
            check_full(int(best['free_prefix_hex'],16),u,len(f));records.append({k:v for k,v in best.items() if k!='free_prefix'})
            print(records[-1],flush=True)
        if time.monotonic()-start>a.seconds:break
    out={'requested_trials':a.trials,'completed_trials':trial+1,'prefix_length':a.prefix,'best':best,
        'records':records,'controls':checked,'best_witness_scalar_and_physical_reencoding_passed':True,
        'search_is_not_exhaustive':True,'Lean_verified':False,'universal_gap_theorem_proved':False,
        'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
    save(f'zero-tail-gap-search-{a.prefix}.json',out)
    print({'completed_trials':trial+1,'best_gap':best['zero_even_gap'],'seconds':out['seconds']},flush=True)

if __name__=='__main__':main()
