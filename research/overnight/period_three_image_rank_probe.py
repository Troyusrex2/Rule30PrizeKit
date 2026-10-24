"""Try a period-three score with an exact finite-preimage domain restriction.

Discovery only: neither recognizer coverage nor any score is Lean verified.
Finite preimages are not unique, so this model uses the recognizer only as
a necessary membership restriction and keeps the score on the current row.
"""
import argparse
from collections import deque
import json
from pathlib import Path
import random
import time

from period_three_finite_preimage_probe import recognizer,accepts,G
from period_three_prefix_graph import Model as Base
from period_three_prefix_rank_probe import Model as Features,good
from stripe_prefix_dfa_potential import add


class Model(Base):
    def __init__(self,r,restrict_front):
        self.r=r;self.size=r+6;self.patterns=1<<r;self.restrict_front=restrict_front
        self.states=48;self.dim=self.states*self.patterns+2
        self.machine=recognizer();initial=self.machine['initial']
        self.sources=set()
        for a in range(1<<(r+2)):
            if a&7 not in (0,7):continue
            for mode in (0,1):self.sources.add((a<<3,24*(a&1)+1,24*mode+1,0,initial))
        reached=set(self.sources);queue=deque(self.sources);self.edges={};reverse={}
        while queue:
            u=queue.popleft();buf,os,ns,depth,image=u;out=[]
            for bit in (0,1):
                full=buf|(bit<<(self.size-1));old=(full>>3)&(self.patterns-1)
                new=self.output(full,depth)
                if depth<3 and (old&1!=os//24 or new&1!=ns//24):continue
                if restrict_front and (not self.valid_front(os,old&1) or not self.valid_front(ns,new&1)):continue
                image_next=self.machine['states'][image]['next'][old&1]
                v=(full>>1,self.advance(os,old&1),self.advance(ns,new&1),min(3,depth+1),image_next)
                edge=(u,v,old,new,bit,depth==0);out.append(edge);reverse.setdefault(v,[]).append(u)
                if v not in reached:reached.add(v);queue.append(v)
            self.edges[u]=out
            if len(reached)>200000:raise RuntimeError('Discovery graph state guard hit; no result claimed')
        self.ends={u for u in reached if u[0]==0 and u[3]==3 and u[1]%2==u[2]%2==0
                   and self.machine['states'][u[4]]['accepting']}
        coreach=set(self.ends);queue=deque(coreach)
        while queue:
            for u in reverse.get(queue.popleft(),[]):
                if u not in coreach:coreach.add(u);queue.append(u)
        self.vertices=reached&coreach;self.sources&=self.vertices
        assert self.sources and self.ends

    def controls(self):
        rng=random.Random(2026102411);finite=Features(self.r,12,True);accepted=0
        for _ in range(100000):
            w=rng.getrandbits(rng.randrange(6,130));w=(w&~7)|rng.choice((0,7));a=G(w);b=G(a)
            assert accepts(a,self.machine)
            if not good(a) or not good(b):continue
            if self.restrict_front and (not self.admissible(a) or not self.admissible(b)):continue
            u=((a&((1<<(self.r+2))-1))<<3,24*(a&1)+1,24*(b&1)+1,0,self.machine['initial'])
            assert u in self.sources;accum={}
            for k in range(a.bit_length()+self.size+18):
                bit=(a>>(k+self.r+2))&1;edge,=[e for e in self.edges[u] if e[4]==bit]
                assert edge[1] in self.vertices
                for j,v in self.gain(edge).items():add(accum,j,v)
                u=edge[1]
            assert u in self.ends
            expected=finite.features(b)
            for j,v in finite.features(a).items():add(expected,j,-v)
            expected={j:v for j,v in expected.items() if v};assert accum==expected
            accepted+=1
            if accepted==128:break
        assert accepted==128
        return {'finite_preimage_domain_and_feature_accounts':accepted,'all_passed':True,
                'coverage_Lean_verified':False}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--radius',type=int,default=2)
    ap.add_argument('--restrict-front',action='store_true');ap.add_argument('--seconds',type=float,default=30)
    args=ap.parse_args();began=time.monotonic();model=Model(args.radius,args.restrict_front)
    checked=model.controls();print(json.dumps({'vertices':len(model.vertices),'controls':checked}),flush=True)
    result=model.solve('flip',args.seconds);result.update(finite_preimage_domain=True,recognizer_states=len(model.machine['states']),
        controls=checked,seconds=round(time.monotonic()-began,3))
    tag='-front' if args.restrict_front else ''
    Path(__file__).with_name('period-three-image-rank-r'+str(args.radius)+tag+'.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in result.items() if k!='candidate'}))
