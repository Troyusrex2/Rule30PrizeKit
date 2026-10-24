"""Synthesize an all-length *candidate* by finite graph-potential inequalities.

The graph is a regular overapproximation of reconstruction ribbons. Its edge
constraints telescope over arbitrarily long words. A floating-point LP result
is never a Lean proof: an accepted result would additionally need exact
rational checks and a kernel-verified graph/word correspondence.
"""
import argparse
from collections import deque
from fractions import Fraction
import json
import math
from pathlib import Path
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, vstack

from reachable_variation_potential import advance, features

HERE=Path(__file__).resolve().parent


def rev(value,width):
    return int(f'{value:0{width}b}'[::-1],2)


def add(out,j,value):
    out[j]=out.get(j,0)+value
    if out[j]==0:del out[j]


class Model:
    def __init__(self,radius,history):
        if radius<3 or history<radius:raise ValueError('Use radius>=3, head history>=radius')
        self.r=radius;self.history=history;self.s=radius-1
        self.small=(1<<self.s)-1;self.full=(1<<radius)-1
        self.patterns=1<<(2*radius-1);self.span=6*self.patterns
        self.headbase=5*self.span;self.dim=self.headbase+10
        self.reverse=[rev(i,radius) for i in range(1<<radius)]
        self.reverse_small=[rev(i,self.s) for i in range(1<<self.s)]
        self.edges={};self.reverse_edges={};self.cases=[]
        for a in range(1<<self.s):
            for b in range(1<<self.s):
                for c in range(1<<self.s):
                    for parity in [0,1]:
                        u=(a,b,c,parity);out=[]
                        for ai in [0,1]:
                            derivative=(a&1)^ai;bp=b&1;bpp=(b>>1)&1
                            if bp>derivative or derivative>(bp|bpp):continue
                            ci=(c&1)^(ai|bp)
                            af=((a<<1)|ai)&self.full;cf=((c<<1)|ci)&self.full
                            old=self.reverse[af]|(self.reverse_small[b]<<radius)
                            new=self.reverse[cf]|(self.reverse_small[af&self.small]<<radius)
                            for bi in [0,1]:
                                v=(af&self.small,((b<<1)|bi)&self.small,cf&self.small,1-parity)
                                edge=(u,v,old,new,ai,bi,ci)
                                out.append(edge);self.reverse_edges.setdefault(v,[]).append(u)
                        self.edges[u]=out
        for phase in [0,1]:
            for age in range(5):
                for head in self.allowed(phase,age):self.cases.append(self.make_case(phase,age,head))

    @staticmethod
    def allowed(phase,age):
        return [1] if phase else [0] if age==4 else [0,1] if age==2 else [1]

    @staticmethod
    def nextage(phase,age,head):
        return (0 if head==0 else min(4,age+1)) if phase==0 else age

    def index(self,phase,age,group,code):
        return age*self.span+phase*3*self.patterns+group*self.patterns+code

    def prefix_vector(self,a,b,length,phase,age):
        result={self.headbase+phase*5+age:1}
        for i in range(length-self.r+1):
            code=((a>>i)&self.full)|(((b>>i)&self.small)<<self.r)
            add(result,self.index(phase,age,0,code),1)
            if i==0:add(result,self.index(phase,age,1,code),1)
        return result

    def full_vector(self,a,b,length,phase,age):
        result=self.prefix_vector(a,b,length,phase,age)
        i=length-self.r
        code=((a>>i)&self.full)|(((b>>i)&self.small)<<self.r)
        add(result,self.index(phase,age,2,code),1)
        return result

    def legal_prefixes(self,phase,age):
        states={(0,0,oldage) for oldage in range(5)}
        for i in range(self.history):
            nxt=set();p=(phase-self.history+i)%2
            for a,b,oldage in states:
                for h in self.allowed(p,oldage):
                    nxt.add((advance(a,b,i,h),a,self.nextage(p,oldage,h)))
            states=nxt
        return sorted((a,b) for a,b,endage in states if endage==age)

    def vertex(self,a,b,c,length):
        s=self.s
        return (rev((a>>(length-s))&self.small,s),
                rev((b>>(length-s))&self.small,s),
                rev((c>>(length+1-s))&self.small,s),length%2)

    def gain(self,case,edge,terminal=False):
        _,_,old,new,*_=edge;phase,age,head=case['key'];na=case['nextage']
        result={}
        add(result,self.index(1-phase,na,0,new),1)
        add(result,self.index(phase,age,0,old),-1)
        if terminal:
            add(result,self.index(1-phase,na,2,new),1)
            add(result,self.index(phase,age,2,old),-1)
        return result

    def terminal(self,edge,phase):
        u,v,old,new,ai,bi,ci=edge;tail=(1<<(self.s-1))-1
        return (v[3]==phase and ai==bi==ci==0 and u[0]&tail==0 and
                u[1]==0 and u[2]&tail==0)

    def make_case(self,phase,age,head):
        na=self.nextage(phase,age,head);sources=[];seen=set();m=self.history
        for a,b in self.legal_prefixes(phase,age):
            c=advance(a,b,m,head)
            vec=self.prefix_vector(c,a,m+1,1-phase,na)
            for j,x in self.prefix_vector(a,b,m,phase,age).items():add(vec,j,-x)
            for last_b in [0,1]:
                u=self.vertex(a,b|(last_b<<(m-1)),c,m)
                marker=(u,tuple(sorted(vec.items())))
                if marker not in seen:sources.append((u,vec));seen.add(marker)
        reached={u for u,_ in sources};queue=deque(reached)
        while queue:
            for edge in self.edges[queue.popleft()]:
                v=edge[1]
                if v not in reached:reached.add(v);queue.append(v)
        ends=[e for u in reached for e in self.edges[u] if self.terminal(e,phase)]
        coreach={e[0] for e in ends};queue=deque(coreach)
        while queue:
            for u in self.reverse_edges.get(queue.popleft(),[]):
                if u not in coreach:coreach.add(u);queue.append(u)
        relevant=reached&coreach
        return {'key':(phase,age,head),'nextage':na,'reward':int(phase==0),
                'sources':[(u,v) for u,v in sources if u in relevant],
                'vertices':relevant,'ends':[e for e in ends if e[0] in relevant]}

    def case_for(self,phase,age,head):
        return next(c for c in self.cases if c['key']==(phase,age,head))

    def check_word(self,a,b,k,age,head):
        c=advance(a,b,k,head);phase=k%2;case=self.case_for(phase,age,head);m=self.history
        expected=self.full_vector(c,a,k+1,1-phase,case['nextage'])
        for j,x in self.full_vector(a,b,k,phase,age).items():add(expected,j,-x)
        ap=a&((1<<m)-1);bp=b&((1<<(m-1))-1);cp=c&((1<<(m+1))-1)
        accum=self.prefix_vector(cp,ap,m+1,1-phase,case['nextage'])
        for j,x in self.prefix_vector(ap,bp,m,phase,age).items():add(accum,j,-x)
        u=self.vertex(a,b,c,m)
        assert any(s==u and v==accum for s,v in case['sources'])
        for i in range(m,k):
            ai=(a>>i)&1;bi=(b>>i)&1;ci=(c>>(i+1))&1
            choices=[e for e in self.edges[u] if e[4:]==(ai,bi,ci)]
            assert len(choices)==1
            edge=choices[0]
            if i==k-1:assert self.terminal(edge,phase)
            for j,x in self.gain(case,edge,i==k-1).items():add(accum,j,x)
            u=edge[1]
            if i<k-1:assert u in case['vertices']
        assert accum==expected,(accum,expected)

    def controls(self,samples=16,depth=513):
        rng=random.Random(20261024);checked=0;bycase=set()
        for _ in range(samples):
            a=b=0;age=2
            for k in range(depth):
                h=rng.choice(self.allowed(k%2,age));c=advance(a,b,k,h)
                if k>self.history and (a>>(k-self.s))==0 and (b>>(k-1-self.s))==0 and (c>>(k+1-self.s))==0:
                    self.check_word(a,b,k,age,h);checked+=1;bycase.add((k%2,age,h))
                a,b,age=c,a,self.nextage(k%2,age,h)
        return {'selected_actual_words':checked,'controller_cases':len(bycase),
                'symbolic_feature_accounting_passed':True}

    def solve(self,seconds):
        rows=[];rhs=[];metadata=[];aux=self.dim;counts=[]
        for case in self.cases:
            rv={v:aux+i for i,v in enumerate(sorted(case['vertices']))};aux+=len(rv)
            n0=len(rows)
            for u,vec in case['sources']:
                row=dict(vec);add(row,rv[u],-1);rows.append(row);rhs.append(-case['reward'])
                metadata.append({'kind':'source','case':case['key'],'vertex':u})
            for u in rv:
                for edge in self.edges[u]:
                    v=edge[1]
                    if v not in rv:continue
                    row=self.gain(case,edge);add(row,rv[u],1);add(row,rv[v],-1)
                    rows.append(row);rhs.append(0)
                    metadata.append({'kind':'bulk','case':case['key'],'edge':edge})
            for edge in case['ends']:
                row=self.gain(case,edge,True);add(row,rv[edge[0]],1);rows.append(row);rhs.append(0)
                metadata.append({'kind':'terminal','case':case['key'],'edge':edge})
            counts.append({'case':case['key'],'vertices':len(rv),'sources':len(case['sources']),
                           'terminal_edges':len(case['ends']),'inequalities':len(rows)-n0})
        values=[];indices=[];indptr=[0]
        for row in rows:
            for j,v in row.items():values.append(v);indices.append(j)
            indptr.append(len(values))
        matrix=csr_matrix((values,indices,indptr),shape=(len(rows),aux),dtype=float)
        self.last_system=(matrix,rhs,rows,metadata)
        objective=np.zeros(aux);objective[:self.dim]=1
        fit=linprog(objective,A_ub=matrix,b_ub=rhs,
                    bounds=[(0,None)]*self.dim+[(None,None)]*(aux-self.dim),
                    method='highs-ds',options={'time_limit':seconds})
        report={'finite_graph_synthesis_only':True,'Lean_proof':False,'CQ01Empty_proved':False,
                'all_length_certificate_form':True,'radius':self.r,'head_history':self.history,
                'white_suffix':self.s,'potential_variables':self.dim,'auxiliary_variables':aux-self.dim,
                'inequalities':len(rows),'cases':counts,'status':int(fit.status),'message':fit.message}
        if fit.success:
            report.update(candidate=fit.x.tolist(),maximum_float_residual=float(np.max(matrix@fit.x-np.array(rhs))),
                          exact_rational_check_passed=False,kernel_check_passed=False)
        return report

    def farkas(self,seconds):
        matrix,rhs,rows,metadata=self.last_system
        # y>=0, y*A_aux=0, y*A_potential>=0, y*b<0 refutes this LP class.
        normalization=csr_matrix(np.array([-b for b in rhs],dtype=float).reshape(1,-1))
        equal=vstack([matrix[:,self.dim:].T,normalization],format='csr')
        target=np.zeros(equal.shape[0]);target[-1]=1
        fit=linprog(np.ones(len(rows)),A_ub=-matrix[:,:self.dim].T,
            b_ub=np.zeros(self.dim),A_eq=equal,b_eq=target,bounds=(0,None),
            method='highs-ds',options={'time_limit':seconds})
        report={'status':int(fit.status),'message':fit.message,'Lean_kernel_checked':False,
                'exact_arithmetic_checked':False,'scope':'this finite graph potential LP only'}
        if not fit.success:return report
        fractions={i:Fraction(float(y)).limit_denominator(1000000) for i,y in enumerate(fit.x) if y>1e-8}
        scale=math.lcm(*(x.denominator for x in fractions.values()))
        integers={i:x.numerator*(scale//x.denominator) for i,x in fractions.items()}
        total={};right=0
        for i,y in integers.items():
            for j,a in rows[i].items():add(total,j,y*a)
            right+=y*rhs[i]
        exact=(all(y>=0 for y in integers.values()) and right<0 and
               all(v==0 for j,v in total.items() if j>=self.dim) and
               all(v>=0 for j,v in total.items() if j<self.dim))
        report.update(exact_arithmetic_checked=exact,scale=scale,right_hand_sum=right,
            support_rows=[{'index':i,'multiplier':y,'row':sorted(rows[i].items()),
                           'rhs':rhs[i],'description':metadata[i]} for i,y in integers.items()],
            remaining_potential_coefficients=sorted((j,v) for j,v in total.items() if j<self.dim),
            remaining_auxiliary_coefficients=sorted((j,v) for j,v in total.items() if j>=self.dim))
        return report

    def set_reward(self,mode):
        for case in self.cases:
            phase,age,head=case['key']
            case['reward']=int(phase==0 and (mode=='cycle' or
                mode=='short-gap' and age==2 and head==0 or
                mode=='long-gap' and age==4 and head==0))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',type=int,default=3)
    ap.add_argument('--head-history',type=int,default=8)
    ap.add_argument('--seconds',type=int,default=120)
    ap.add_argument('--reward',choices=['cycle','short-gap','long-gap'],default='cycle')
    ap.add_argument('--farkas',action='store_true',help='Try an exact arithmetic refutation of the LP class')
    args=ap.parse_args();started=time.monotonic()
    model=Model(args.radius,args.head_history)
    model.set_reward(args.reward)
    controls=model.controls();print(json.dumps({'stage':'controls','result':controls}),flush=True)
    report=model.solve(args.seconds);report['controls']=controls;report['reward_mode']=args.reward
    if args.farkas and report['status']==2:report['farkas']=model.farkas(args.seconds)
    report['seconds']=round(time.monotonic()-started,3)
    suffix='-'+args.reward if args.reward!='cycle' else ''
    target=HERE/f'transducer-potential-r{args.radius}-head{args.head_history}{suffix}.json'
    target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['candidate','cases','farkas']} |
        {'exact_LP_refutation':report.get('farkas',{}).get('exact_arithmetic_checked',False)}))


if __name__=='__main__':main()
