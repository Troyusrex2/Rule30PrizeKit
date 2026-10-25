"""Complete sparse-even tree under a finite right-language window guard.

The guard is an overapproximation derived from a numerical complete image,
not a Lean assumption. State caps retain UNKNOWN. Any charge counterexample
is separately queried against the actual right dynamics before use.
"""
import argparse,hashlib,json,time
from core import HERE,save
from charge_beam_packed import step,controls,check_full
from right_image_smt import make
import z3
from empty_right_absorption import step as right_step

def main():
    p=argparse.ArgumentParser();p.add_argument('--budget',type=int,default=12)
    p.add_argument('--window',type=int,default=30);p.add_argument('--states',type=int,default=250000)
    p.add_argument('--depth',type=int,default=256);p.add_argument('--seconds',type=float,default=200)
    a=p.parse_args();start=time.monotonic();checked=controls()
    source=HERE/f'right-image-smt-{a.window}.json'
    if not source.exists():source=HERE/'right-image-smt-30.json'
    raw=source.read_bytes();ref=json.loads(raw)
    assert ref['finite_census_complete'] and a.window<=ref['length']
    image={int(w)&((1<<a.window)-1) for w in ref['image_witnesses']}
    allowed=[{w&((1<<k)-1) for w in image} for k in range(a.window+1)]
    states=[(0,0,0,0,0,0)];records=[];candidates=[];lowest=0;reason='depth_cap';complete_depth=0
    maxima=[{'black_evens':k,'zeros':-1} for k in range(a.budget+1)]
    maxima[0].update({'zeros':0,'length':0,'even_input_hex':'0x0','free_prefix_hex':'0x0'})
    for d in range(a.depth):
        nxt=[];mask=(1<<(2*d+2))-1;overflow=False
        for R,Rm,u,w,cost,zeros in states:
            R1,old=step(R,Rm,2*d,1);base,_=step(R1,old,2*d+1,0);pred=(base>>(2*d+1))&1
            for e in range(1+(cost<a.budget)):
                s=pred^e;nw=w|(s<<d)
                if d+1<a.window:
                    if nw not in allowed[d+1]:continue
                elif nw>>(d+1-a.window)&((1<<a.window)-1) not in image:continue
                ncost=cost+e;nzeros=zeros+1-s;score=3*ncost-nzeros
                if nzeros>maxima[ncost]['zeros']:
                    maxima[ncost]={'black_evens':ncost,'zeros':nzeros,'length':d+1,
                        'even_input_hex':hex(u|(e<<d)),'free_prefix_hex':hex(nw)}
                if score<lowest:
                    lowest=score;f=check_full(nw,u|(e<<d),d+1)
                    rec={'length':d+1,'deficit':score,'free_prefix_hex':hex(nw),
                        'even_input_hex':hex(u|(e<<d)),'zeros':nzeros,'black_evens':ncost}
                    candidates.append(rec);print({'candidate':rec},flush=True)
                nxt.append((base^(mask if s else 0),R1,u|(e<<d),nw,ncost,nzeros))
                if len(nxt)>a.states:overflow=True;break
            if overflow:break
        if overflow:reason='state_cap';break
        states=nxt;complete_depth=d+1;records.append({'depth':d+1,'states':len(states)})
        if (d+1)%16==0 or not states:print(records[-1],flush=True)
        if not states:reason='complete_extinction';break
        if time.monotonic()-start>a.seconds:reason='self_time_limit';break
    # Cap the extra realization work; a timeout is never called nonrealizability.
    for rec in candidates[-3:]:
        n=rec['length'];w=int(rec['free_prefix_hex'],16);solver,initial,cols=make(n)
        solver.set(timeout=5000)
        solver.add(*[q==bool(w>>j&1) for j,q in enumerate(cols)])
        status=solver.check();rec['actual_right_realization']=str(status)
        if status==z3.sat:
            m=solver.model();R=sum(int(z3.is_true(m.eval(q,model_completion=True)))<<j for j,q in enumerate(initial))
            x=R;f=[]
            for t in range(2*n-1):
                x=right_step(x,t)
                if t%2==0:f.append(1^(x&1))
            assert sum(s<<j for j,s in enumerate(f))==w
            rec['right_initial_hex']=hex(R);rec['independent_right_check_passed']=True
        if status==z3.unknown:rec['reason_unknown']=solver.reason_unknown()
    for rec in maxima:
        if rec['zeros']>=0:
            check_full(int(rec['free_prefix_hex'],16),int(rec['even_input_hex'],16),rec['length'])
    out={'budget':a.budget,'window':a.window,'state_cap':a.states,'last_complete_depth':complete_depth,
        'stop_reason':reason,'complete_extinction':reason=='complete_extinction','records':records,
        'charge_candidates':candidates,'lowest_factor3_deficit':lowest,'controls':checked,
        'image_source_sha256':hashlib.sha256(raw).hexdigest(),'image_census_length':ref['length'],
        'window_image_words':len(image),
        'maximum_zeros_by_exact_even_cost':maxima,'maxima_complete':reason=='complete_extinction',
        'extremal_prefixes_independently_reencoded':True,
        'language_guard_numerical_only':True,'Lean_verified':False,'unbounded_charge_proved':False,
        'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
    save(f'sparse-coupled-budget{a.budget}-window{a.window}.json',out)
    print({k:v for k,v in out.items() if k not in ('records','charge_candidates','controls')},flush=True)

if __name__=='__main__':main()
