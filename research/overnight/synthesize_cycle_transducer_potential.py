"""Two-step transducer-potential synthesis; no numerical result is a Lean proof."""
import argparse
import json
import time

import numpy as np

from reachable_variation_potential import advance
from synthesize_transducer_potential import HERE, Model, add, rev


class CycleModel(Model):
    def __init__(self,radius,history):
        if radius<3 or history<radius:raise ValueError('Use radius>=3, history>=radius')
        self.r=radius;self.history=history;self.s=radius-1
        self.small=(1<<self.s)-1;self.full=(1<<radius)-1
        self.patterns=1<<(2*radius-1);self.span=3*self.patterns
        self.headbase=5*self.span;self.dim=self.headbase+5
        self.reverse=[rev(i,radius) for i in range(1<<radius)]
        self.reverse_small=[rev(i,self.s) for i in range(1<<self.s)]
        self.edges={};self.reverse_edges={};self.cases=[]
        for a in range(1<<self.s):
            for b in range(1<<self.s):
                for c in range(1<<self.s):
                    for d in range(1<<self.s):
                        for parity in [0,1]:
                            u=(a,b,c,d,parity);out=[]
                            for ai in [0,1]:
                                derivative=(a&1)^ai;bp=b&1;bpp=(b>>1)&1
                                if bp>derivative or derivative>(bp|bpp):continue
                                ci=(c&1)^(ai|bp)
                                di=(d&1)^(ci|ai)
                                af=((a<<1)|ai)&self.full;cf=((c<<1)|ci)&self.full
                                df=((d<<1)|di)&self.full
                                old=self.reverse[af]|(self.reverse_small[b]<<radius)
                                new=self.reverse[df]|(self.reverse_small[cf&self.small]<<radius)
                                for bi in [0,1]:
                                    v=(af&self.small,((b<<1)|bi)&self.small,cf&self.small,df&self.small,1-parity)
                                    edge=(u,v,old,new,ai,bi,ci,di)
                                    out.append(edge);self.reverse_edges.setdefault(v,[]).append(u)
                            self.edges[u]=out
        for age in range(5):
            for head in self.allowed(0,age):self.cases.append(self.make_case(0,age,head))

    def index(self,phase,age,group,code):
        return age*self.span+group*self.patterns+code

    def prefix_vector(self,a,b,length,phase,age):
        result={self.headbase+age:1}
        for i in range(length-self.r+1):
            code=((a>>i)&self.full)|(((b>>i)&self.small)<<self.r)
            add(result,self.index(0,age,0,code),1)
            if i==0:add(result,self.index(0,age,1,code),1)
        return result

    def vertex(self,a,b,c,d,length):
        s=self.s
        return (rev((a>>(length-s))&self.small,s),rev((b>>(length-s))&self.small,s),
                rev((c>>(length+1-s))&self.small,s),rev((d>>(length+2-s))&self.small,s),length%2)

    def terminal(self,edge,phase):
        u,v,old,new,ai,bi,ci,di=edge;tail=(1<<(self.s-1))-1
        return (v[4]==0 and ai==bi==ci==di==0 and u[0]&tail==0 and
                u[1]==0 and u[2]&tail==0 and u[3]&tail==0)

    def make_case(self,phase,age,head):
        from collections import deque
        na=self.nextage(0,age,head);sources=[];seen=set();m=self.history
        for a,b in self.legal_prefixes(0,age):
            c=advance(a,b,m,head);d=advance(c,a,m+1,1)
            vec=self.prefix_vector(d,c,m+2,0,na)
            for j,x in self.prefix_vector(a,b,m,0,age).items():add(vec,j,-x)
            for last_b in [0,1]:
                u=self.vertex(a,b|(last_b<<(m-1)),c,d,m)
                marker=(u,tuple(sorted(vec.items())))
                if marker not in seen:sources.append((u,vec));seen.add(marker)
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
        return {'key':(0,age,head),'nextage':na,'reward':1,
                'sources':[(u,v) for u,v in sources if u in relevant],
                'vertices':relevant,'ends':[e for e in ends if e[0] in relevant]}

    def check_word(self,a,b,k,age,head):
        c=advance(a,b,k,head);d=advance(c,a,k+1,1);case=self.case_for(0,age,head);m=self.history
        expected=self.full_vector(d,c,k+2,0,case['nextage'])
        for j,x in self.full_vector(a,b,k,0,age).items():add(expected,j,-x)
        ap=a&((1<<m)-1);bp=b&((1<<(m-1))-1)
        cp=c&((1<<(m+1))-1);dp=d&((1<<(m+2))-1)
        accum=self.prefix_vector(dp,cp,m+2,0,case['nextage'])
        for j,x in self.prefix_vector(ap,bp,m,0,age).items():add(accum,j,-x)
        u=self.vertex(a,b,c,d,m)
        assert any(s==u and v==accum for s,v in case['sources'])
        for i in range(m,k):
            data=((a>>i)&1,(b>>i)&1,(c>>(i+1))&1,(d>>(i+2))&1)
            choices=[e for e in self.edges[u] if e[4:]==data]
            assert len(choices)==1
            edge=choices[0]
            if i==k-1:assert self.terminal(edge,0)
            for j,x in self.gain(case,edge,i==k-1).items():add(accum,j,x)
            u=edge[1]
            if i<k-1:assert u in case['vertices']
        assert accum==expected,(accum,expected)

    def controls(self,samples=16,depth=257):
        import random
        rng=random.Random(20261024);checked=0;bycase=set()
        for _ in range(samples):
            a=b=0;age=2
            for cycle in range(depth):
                k=2*cycle;h=rng.choice(self.allowed(0,age))
                c=advance(a,b,k,h);d=advance(c,a,k+1,1)
                if (k>self.history and (a>>(k-self.s))==0 and (b>>(k-1-self.s))==0 and
                        (c>>(k+1-self.s))==0 and (d>>(k+2-self.s))==0):
                    self.check_word(a,b,k,age,h);checked+=1;bycase.add((age,h))
                a,b,age=d,c,self.nextage(0,age,h)
        return {'selected_actual_words':checked,'controller_cases':len(bycase),
                'symbolic_feature_accounting_passed':True}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',type=int,default=3)
    ap.add_argument('--head-history',type=int,default=8)
    ap.add_argument('--seconds',type=int,default=120)
    ap.add_argument('--reward',choices=['cycle','short-gap','long-gap'],default='cycle')
    ap.add_argument('--farkas',action='store_true')
    args=ap.parse_args();started=time.monotonic()
    model=CycleModel(args.radius,args.head_history)
    model.set_reward(args.reward)
    controls=model.controls();print(json.dumps({'stage':'controls','result':controls}),flush=True)
    report=model.solve(args.seconds);report.update(controls=controls,grouped_reconstruction_steps=2,reward_mode=args.reward,
        seconds=round(time.monotonic()-started,3))
    if args.farkas and report['status']==2:report['farkas']=model.farkas(args.seconds)
    suffix='-'+args.reward if args.reward!='cycle' else ''
    target=HERE/f'cycle-transducer-potential-r{args.radius}-head{args.head_history}{suffix}.json'
    target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['candidate','cases','farkas']} |
        {'exact_LP_refutation':report.get('farkas',{}).get('exact_arithmetic_checked',False)}))


if __name__=='__main__':main()
