"""Falsify the factor-three target on periodic words with the checked guards.

Periodic examples test a different failure path from greedy beam searches.
No observed density or nonfailure is promoted to an infinite theorem.
"""
import argparse,time
from core import save
from even_code_charge import words
from charge_beam_packed import step,controls
from coupled_even_code_probe import decode

def main():
    p=argparse.ArgumentParser();p.add_argument('--max-period',type=int,default=14)
    p.add_argument('--horizon',type=int,default=2048);p.add_argument('--seconds',type=float,default=180)
    a=p.parse_args();start=time.monotonic();checked=controls();records=[];counters=[];stopped=False;total=0
    banned=['00','11111','010110','1011010']
    for n in range(1,a.max_period+1):
        count=0;best=None
        for w in words(n,True):
            f=[w>>j&1 for j in range(n)]
            if any(n%d==0 and all(f[j]==f[j%d] for j in range(n)) for d in range(1,n)):continue
            cyclic=''.join(map(str,(f*((n+6)//n+2))[:2*n+6]))
            if any(any(cyclic[j:j+len(q)]==q for j in range(n)) for q in banned):continue
            R=Rm=E=z=cost=0;worst=0;first=None
            for d in range(a.horizon):
                s=f[d%n];R1,old=step(R,Rm,2*d,1);R,Rm=step(R1,old,2*d+1,s)
                e=(R>>(2*d+1))&1;E|=e<<d;z+=1-s;cost+=e;score=3*cost-z
                if score<worst:
                    worst=score
                    if first is None:first={'prefix':d+1,'deficit':score,'even_input_hex':hex(E)}
            assert decode(E&((1<<64)-1),min(64,a.horizon))==[f[j%n] for j in range(min(64,a.horizon))]
            count+=1;total+=1;rec={'period':n,'word_time_first':''.join(map(str,f)),
                'horizon':a.horizon,'final_deficit':3*cost-z,'even_black_count':cost,'free_zeros':z,
                'minimum_deficit':worst}
            if first is not None:counters.append({**rec,'first_counterexample':first});print({'counterexample':counters[-1]},flush=True)
            if best is None or rec['final_deficit']<best['final_deficit']:best=rec
            if time.monotonic()-start>a.seconds:stopped=True;break
        records.append({'period':n,'primitive_phases_checked':count,'best_final':best,'period_census_complete':not stopped})
        print(records[-1],flush=True)
        if stopped:break
    out={'max_period':a.max_period,'horizon':a.horizon,'primitive_phases_checked':total,
        'guard_words':banned,'records':records,'counterexamples':counters,'search_complete_to_requested_period':not stopped,
        'controls':checked,'each_word_first64_physical_decode_checked':True,'Lean_verified':False,
        'unbounded_charge_proved':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
    save(f'periodic-charge-seven-period{a.max_period}.json',out)

if __name__=='__main__':main()
