"""Finite predictive-state diagnostic for the period-three constrained left half.

This explores a new recognizer candidate, not a proved finite-state model.
Exact finite trie counts do not establish regularity or nonregularity of the
infinite language and do not prove any Rule 30 Prize problem.
"""
import argparse
import json
from pathlib import Path
import random
import time


def step(a,b):return (a>>1)^(a|(a<<1)|b)


def head_at(a,t):
    for j in range(t):a=step(a,int(j%3==1))
    return a&1


def build(n):
    levels=[[0]];children=[]
    for t in range(n):
        new=[];links=[]
        target=None if t%3==0 else int(t%3==2)
        for a in levels[-1]:
            if target is None:
                links.append((len(new),len(new)+1));new.extend((a,a|(1<<t)))
            else:
                bit=head_at(a,t)^target
                ix=len(new);new.append(a|(bit<<t));links.append((ix,-1) if bit==0 else (-1,ix))
        levels.append(new);children.append(links)
        assert len(new)==1<<((t+3)//3)
    assert set(levels[3])=={0,7}
    assert set(levels[6])=={31,32,55,56}
    return levels,children


def controls(levels):
    rng=random.Random(2026102409);checked=0
    for t in range(1,len(levels)):
        for a in rng.sample(levels[t],min(8,len(levels[t]))):
            row=a
            for j in range(t):
                if j%3:assert row&1==int(j%3==2)
                row=step(row,int(j%3==1))
            checked+=1
    return {'independent_full_history_samples':checked,'all_passed':True}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--depth',type=int,default=42)
    ap.add_argument('--future',type=int,default=15);args=ap.parse_args()
    assert 6<=args.depth<=48 and 3<=args.future<=18
    began=time.monotonic();levels,children=build(args.depth);checked=controls(levels)
    previous=[[0]*len(v) for v in levels];results=[]
    for horizon in range(1,args.future+1):
        dictionary={};current=[]
        for depth in range(args.depth-horizon+1):
            ids=[]
            for c0,c1 in children[depth]:
                signature=(previous[depth+1][c0] if c0>=0 else -1,
                           previous[depth+1][c1] if c1>=0 else -1)
                if signature not in dictionary:dictionary[signature]=len(dictionary)
                ids.append(dictionary[signature])
            current.append(ids)
            if depth%3==0 and horizon%3==0:
                results.append({'prefix_depth':depth,'future_cells':horizon,
                                'valid_prefixes':len(levels[depth]),
                                'different_allowed_future_subtrees':len(set(ids))})
        previous=current
    report={'finite_experiment_only':True,'Lean_verified':False,'full_problem_claim':False,
            'C3w_011_proved':False,'regularity_proved':False,'nonregularity_proved':False,
            'depth':args.depth,'future':args.future,'controls':checked,'cases':results,
            'seconds':round(time.monotonic()-began,3)}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':main()
