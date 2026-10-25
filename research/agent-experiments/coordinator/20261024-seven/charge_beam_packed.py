"""Fast packed-anti-diagonal charge falsification, with independent controls.

This beam is heuristic. Failure to find a counterexample proves nothing.
The prefix-xor scan is checked against scalar lists and physical evolution.
"""
import argparse,random,time
from core import save
from coupled_even_code_probe import decode,forbidden
from zero_tail_rank import step as scalar_step

def step(R,Rm,L,y):
    mask=(1<<L)-1;v=(R|(Rm<<1))&mask;shift=1
    while shift<L:v^=v<<shift;shift*=2
    v&=mask
    return y|((v^(mask if y else 0))<<1),R

def controls():
    rng=random.Random(302459);count=0
    for _ in range(32):
        a=[];b=[];R=Rm=L=0;u=0;free=[]
        for d in range(32):
            R,Rm=step(R,Rm,L,1);L+=1;a,b=scalar_step(a,b,1)
            assert R==sum(x<<i for i,x in enumerate(a))
            y=rng.randrange(2);R,Rm=step(R,Rm,L,y);L+=1;a,b=scalar_step(a,b,y)
            assert R==sum(x<<i for i,x in enumerate(a));count+=L
            u|=(R>>(L-1)&1)<<d;free.append(y)
        assert decode(u,32)==free
    return {'scalar_list_cells':count,'physical_decoder_cases':32,'all_passed':True}

def check_full(word,u,n):
    free=[word>>i&1 for i in range(n)];assert forbidden(free) is None
    R=[];Rm=[];v=0
    for d,s in enumerate(free):
        R,Rm=scalar_step(R,Rm,1);R,Rm=scalar_step(R,Rm,s);v|=R[-1]<<d
    assert v==u and decode(u,min(n,64))==free[:64]
    return free

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--length',type=int,default=2048)
    parser.add_argument('--beam',type=int,default=2048);parser.add_argument('--factor',type=int,default=8)
    parser.add_argument('--seconds',type=float,default=210);args=parser.parse_args()
    checked=controls();start=time.monotonic();states=[(0,0,0,0,0,0,0)];records=[]
    out={'beam_width':args.beam,'factor':args.factor,'requested_length':args.length,
         'controls':checked,'records':records,'search_heuristic_not_exhaustive':True,
         'Lean_verified':False,'uniform_rank_proved':False,'full_problem_solved':False}
    stopped='length_completed'
    for d in range(args.length):
        choices=[];mask=(1<<(2*d+2))-1
        for R,Rm,u,word,zeros,run,cost in states:
            R1,Rold=step(R,Rm,2*d,1);base,_=step(R1,Rold,2*d+1,0);pred=base>>(2*d+1)&1
            for s in (0,1):
                if (s==0 and d and run==0) or (s==1 and run==4):continue
                bit=pred^s
                choices.append((base^(mask if s else 0),R1,u|(bit<<d),word|(s<<d),
                                zeros+1-s,run+1 if s else 0,cost+bit))
        choices.sort(key=lambda a:(args.factor*a[6]-a[4],a[6],a[2]))
        states=choices[:args.beam];best=states[0];score=args.factor*best[6]-best[4]
        if (d+1)%64==0 or score<0 or d+1==args.length:
            row={'length':d+1,'best_deficit':score,'even_black_count':best[6],
                 'free_zeros':best[4],'finite_even_input_hex':hex(best[2]),
                 'free_prefix_hex':hex(best[3]),'seconds':round(time.monotonic()-start,3)}
            records.append(row);out['counterexample_found']=score<0
            save(f'charge-packed-factor{args.factor}.json',out)
            print({k:v for k,v in row.items() if not k.endswith('_hex')},flush=True)
        if score<0:stopped='counterexample_found';break
        if time.monotonic()-start>args.seconds:stopped='time_budget';break
    free=check_full(best[3],best[2],d+1)
    out.update({'stop_reason':stopped,'completed_length':d+1,'counterexample_found':score<0,
                'final_prefix_scalar_reencoding_passed':True,'final_free_prefix':free,
                'final_input_hex':hex(best[2]),'final_even_black_count':best[6],
                'final_free_zeros':best[4],'final_deficit':score,
                'seconds':round(time.monotonic()-start,3)})
    save(f'charge-packed-factor{args.factor}.json',out)
    print({'stop_reason':stopped,'completed_length':d+1,'score':score,'independent_reencoding':True},flush=True)

if __name__=='__main__':main()
