"""Heuristic falsification of an unbounded variation/weight estimate.

Beam pruning is not sound for universal claims. Every found counterexample is
checked by ordinary forward evolution, and is still a finite observation.
"""
import argparse
import json
from pathlib import Path
import random
import time


def prefix_xor(value, bits):
    shift=1
    while shift<bits:
        value ^= value<<shift
        shift*=2
    return value & ((1<<bits)-1)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth',type=int,default=1025)
    ap.add_argument('--beam',type=int,default=2048)
    ap.add_argument('--multiplier',type=int,default=2)
    ap.add_argument('--continue-after-counter',action='store_true')
    args=ap.parse_args()
    # r, rm, variation, weight, last_free, free_prefix, initial_prefix
    states=[(0,0,0,0,-1,0,0)]
    began=time.monotonic();rng=random.Random(20261024)
    report={'heuristic_only':True,'unbounded_estimate_proved':False,'beam':args.beam,
            'multiplier':args.multiplier,'seed':20261024,'levels':[],'counterexample':None}
    suffix='-long' if args.continue_after_counter else ''
    target=Path(__file__).parent/f'variation-weight-beam-c{args.multiplier}{suffix}.json'
    best_counter_score=0
    for k in range(args.depth):
        mask=(1<<k)-1
        next_states=[]
        for r,rm,var,weight,last,free,initial in states:
            scan=prefix_xor(r|(rm<<1),k)
            for b in ([1] if k%2==0 else [0,1]):
                nxt=((scan^(mask if b else 0))<<1)|b
                cell=(nxt>>k)&1
                nv=var+int(k%2==1 and last>=0 and last!=b)
                nf=free|(b<<(k//2)) if k%2 else free
                ns=(nxt,r,nv,weight+cell,b if k%2 else last,nf,initial|(cell<<k))
                next_states.append(ns)
                score=nv-args.multiplier*(weight+cell)
                if k%2==0 and score>best_counter_score:
                    row=ns[-1];f=ns[-2]
                    for t in range(k+1):
                        assert row&1 == (1 if t%2==0 else (f>>(t//2))&1)
                        row=(row>>1)^(row|(row<<1))
                    report['counterexample']={'depth':k+1,'changes':nv,'black_weight':weight+cell,
                        'free_prefix':''.join(str((f>>j)&1) for j in range((k+1)//2)),
                        'initial_prefix':''.join(str((ns[-1]>>j)&1) for j in range(k+1)),
                        'independently_checked':True}
                    best_counter_score=score
                    target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
                    print(json.dumps({k:v for k,v in report['counterexample'].items()
                                      if k not in ['free_prefix','initial_prefix']}),flush=True)
                    if not args.continue_after_counter:
                        return
        # Exact future state equality permits retaining the best prefix metric;
        # beam truncation still makes the overall search incomplete.
        best={}
        for s in next_states:
            key=(s[0],s[1],s[4]);score=s[2]-args.multiplier*s[3]
            if key not in best or score>best[key][0]:best[key]=(score,s)
        ranked=[(score,rng.random(),s) for score,s in best.values()]
        ranked.sort(reverse=True)
        states=[s for _,_,s in ranked[:args.beam]]
        if k%2==0:
            row={'depth':k+1,'best_score':ranked[0][0],'retained':len(states)}
            report['levels'].append(row)
            if k%64==0:
                report['seconds']=round(time.monotonic()-began,3)
                target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
                print(json.dumps(row),flush=True)
    report['seconds']=round(time.monotonic()-began,3)
    target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'no_counterexample_in_beam':report['counterexample'] is None,
                      'depth':args.depth,'best_counter_score':best_counter_score,'seconds':report['seconds']}))


if __name__=='__main__':main()
