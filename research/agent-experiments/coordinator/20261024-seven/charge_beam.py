"""Targeted falsification of factor-three charge beyond exhaustive prefixes.

The beam is a search heuristic. A missed counterexample proves nothing.
Found prefixes are independently re-encoded with the skelPair recurrence.
"""
import argparse,json,time
from core import HERE,save
from coupled_even_code_probe import even_code,decode,forbidden,packed_run

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--length',type=int,default=256)
    parser.add_argument('--beam',type=int,default=512);parser.add_argument('--factor',type=int,default=3)
    args=parser.parse_args();start=time.monotonic()
    # row, even input, free word, zero count, final one run, even black count
    states=[(0,0,0,0,0,0)]
    out={'beam_width':args.beam,'factor':args.factor,'records':[],
         'search_heuristic_not_exhaustive':True,'Lean_verified':False,'full_problem_solved':False}
    for d in range(args.length):
        choices=[]
        for row,u,word,zeros,run,cost in states:
            odd=1^(packed_run(row,2*d)&1);rowodd=row|(odd<<(2*d))
            predicted=packed_run(rowodd,2*d+1)&1
            for s in (0,1):
                if (s==0 and d>0 and run==0) or (s==1 and run==4):continue
                bit=predicted^s
                choices.append((rowodd|(bit<<(2*d+1)),u|(bit<<d),word|(s<<d),
                                zeros+(1-s),run+1 if s else 0,cost+bit))
        choices.sort(key=lambda st:(args.factor*st[5]-st[3],st[5],st[1]))
        states=choices[:args.beam];best=states[0];score=args.factor*best[5]-best[3]
        if (d+1)%16==0 or score<0:
            free=[(best[2]>>i)&1 for i in range(d+1)]
            assert forbidden(free) is None and even_code(free)==best[1] and decode(best[1],d+1)==free
            row={'length':d+1,'retained_states':len(states),'best_deficit':score,
                 'even_black_count':best[5],'free_zeros':best[3],'finite_even_input':best[1],
                 'free_prefix':free,'seconds':round(time.monotonic()-start,3)}
            out['records'].append(row)
            save(f'charge-beam-factor{args.factor}.json',out)
            print({k:v for k,v in row.items() if k!='free_prefix'},flush=True)
        if score<0:
            out['counterexample_found']=True;break
    else:out['counterexample_found']=False
    out['seconds']=round(time.monotonic()-start,3);save(f'charge-beam-factor{args.factor}.json',out)

if __name__=='__main__':main()
