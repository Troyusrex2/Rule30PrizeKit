"""Unbounded-form graph LP with a stronger, provisional empty-gate controller.

No search result is a proof. A successful candidate would require kernel checks
of both the controller extraction and the telescoping potential certificate.
"""
import argparse
from collections import deque
import json
import random
import time

from empty_gate_controller import make_controller
from reachable_variation_potential import advance
from synthesize_cycle_transducer_potential import CycleModel
from synthesize_transducer_potential import HERE, add


class ControlledModel(CycleModel):
    def __init__(self,radius,history,controller,reward):
        base=CycleModel(radius,history)
        self.__dict__.update(base.__dict__)
        self.controller=controller;self.words=controller['words'];self.length=controller['length']
        self.lookup={w:i for i,w in enumerate(self.words)};self.mask=(1<<self.length)-1
        self.headbase=len(self.words)*self.span;self.dim=self.headbase+len(self.words)
        self.reward_mode=reward;self.cases=[]
        if self.length<history//2+1 or history%2:raise ValueError('Controller must contain the recent gate history')
        self.transitions=[]
        for w in controller['transition_words']:
            old=w&self.mask;new=w>>1
            self.transitions.append((self.lookup[old],self.lookup[new]))
        for old,new in self.transitions:self.cases.append(self.make_controlled_case(old,new))
        self.case_lookup={(c['key'][1],c['key'][2]):c for c in self.cases}

    def make_controlled_case(self,old,new):
        word=self.words[old];m=self.history;a=b=0
        h=1-((word>>(self.length-1))&1)
        for j in range(m//2):
            past=(word>>(self.length-1-m//2+j))&1
            c=advance(a,b,2*j,1-past);d=advance(c,a,2*j+1,1);a,b=d,c
        c=advance(a,b,m,h);d=advance(c,a,m+1,1)
        vec=self.prefix_vector(d,c,m+2,0,new)
        for j,x in self.prefix_vector(a,b,m,0,old).items():add(vec,j,-x)
        sources=[]
        for last_b in [0,1]:sources.append((self.vertex(a,b|(last_b<<(m-1)),c,d,m),dict(vec)))
        reached={u for u,_ in sources};queue=deque(reached)
        while queue:
            for edge in self.edges[queue.popleft()]:
                v=edge[1]
                if v not in reached:reached.add(v);queue.append(v)
        ends=[e for u in reached for e in self.edges[u] if self.terminal(e,0)]
        coreach={e[0] for e in ends};queue=deque(coreach)
        while queue:
            for u in self.reverse_edges.get(queue.popleft(),[]):
                if u not in coreach:coreach.add(u);queue.append(u)
        relevant=reached&coreach
        current=(word>>(self.length-1))&1
        offset=3 if self.reward_mode=='short-gap' else 5
        reward=1 if self.reward_mode=='cycle' else int(current and ((word>>(self.length-1-offset))&1))
        return {'key':(0,old,new),'nextage':new,'reward':reward,
                'sources':[(u,v) for u,v in sources if u in relevant],
                'vertices':relevant,'ends':[e for e in ends if e[0] in relevant]}

    def check_controlled_word(self,a,b,k,old,new):
        h=1-((self.words[old]>>(self.length-1))&1)
        c=advance(a,b,k,h);d=advance(c,a,k+1,1);case=self.case_lookup[(old,new)];m=self.history
        expected=self.full_vector(d,c,k+2,0,new)
        for j,x in self.full_vector(a,b,k,0,old).items():add(expected,j,-x)
        ap=a&((1<<m)-1);bp=b&((1<<(m-1))-1)
        cp=c&((1<<(m+1))-1);dp=d&((1<<(m+2))-1)
        accum=self.prefix_vector(dp,cp,m+2,0,new)
        for j,x in self.prefix_vector(ap,bp,m,0,old).items():add(accum,j,-x)
        u=self.vertex(a,b,c,d,m)
        assert any(s==u and v==accum for s,v in case['sources'])
        for i in range(m,k):
            data=((a>>i)&1,(b>>i)&1,(c>>(i+1))&1,(d>>(i+2))&1)
            choices=[e for e in self.edges[u] if e[4:]==data];assert len(choices)==1
            edge=choices[0]
            if i==k-1:assert self.terminal(edge,0)
            for j,x in self.gain(case,edge,i==k-1).items():add(accum,j,x)
            u=edge[1]
            if i<k-1:assert u in case['vertices']
        assert accum==expected

    def controls(self,samples=16,depth=513):
        rng=random.Random(20261024);checked=0;bycase=set()
        vals=self.controller['core_states'];succ=self.controller['successors']
        for _ in range(samples):
            q=rng.randrange(len(vals));bits=[]
            for j in range(self.length):
                bits.append(vals[q]&1)
                if j+1<self.length:q=rng.choice(succ[q])
            word=sum(x<<i for i,x in enumerate(bits));a=b=0
            for cycle in range(depth):
                k=2*cycle;old=self.lookup[word];qn=rng.choice(succ[q]);nbit=vals[qn]&1
                nextword=(word>>1)|(nbit<<(self.length-1));new=self.lookup[nextword]
                assert (old,new) in self.case_lookup
                h=1-(vals[q]&1);c=advance(a,b,k,h);d=advance(c,a,k+1,1)
                if (k>self.history and a>>(k-self.s)==0 and b>>(k-1-self.s)==0 and
                        c>>(k+1-self.s)==0 and d>>(k+2-self.s)==0):
                    self.check_controlled_word(a,b,k,old,new);checked+=1;bycase.add((old,new))
                a,b=d,c;word=nextword;q=qn
        return {'selected_controller_words':checked,'controller_transitions_seen':len(bycase),
                'symbolic_feature_accounting_passed':True}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',type=int,default=3)
    ap.add_argument('--head-history',type=int,default=8)
    ap.add_argument('--controller-length',type=int,default=7)
    ap.add_argument('--reward',choices=['cycle','short-gap','long-gap'],default='short-gap')
    ap.add_argument('--seconds',type=int,default=120)
    args=ap.parse_args();started=time.monotonic()
    controller=make_controller(args.controller_length)
    print(json.dumps({'stage':'controller','states':len(controller['words']),
                      'transitions':len(controller['transition_words']),'provisionally_extracted_core':len(controller['core_states'])}),flush=True)
    model=ControlledModel(args.radius,args.head_history,controller,args.reward)
    controls=model.controls();print(json.dumps({'stage':'controls','result':controls}),flush=True)
    report=model.solve(args.seconds);report.update(controls=controls,reward=args.reward,
        controller=controller,controller_Lean_verified=False,grouped_steps=2,seconds=round(time.monotonic()-started,3))
    target=HERE/f'controlled-transducer-r{args.radius}-head{args.head_history}-memory{args.controller_length}-{args.reward}.json'
    target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['controller','cases','candidate']}))


if __name__=='__main__':main()
