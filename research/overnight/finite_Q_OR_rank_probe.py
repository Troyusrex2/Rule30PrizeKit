"""Seek a finite-tail Q flux score, without a positivity premise.

Q preserves finite width and has periodic finite orbits. Therefore a score
nonincreasing on constant-head-OR transitions, strictly falling when the head
does not flip, could exclude such an event by summing around the orbit.
This program is discovery only; graph coverage and certificates need Lean.
"""
import argparse
from collections import deque
from fractions import Fraction
import json
from pathlib import Path
import random
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from stripe_prefix_dfa_potential import add


def q(a):return a^((a>>1)|(a>>2))


class Model:
    def __init__(self,r,stride=1):
        assert 2<=r<=6
        self.r=r;self.stride=stride;self.patterns=1<<r;self.size=r+2*stride;self.dim=9*self.patterns
        self.sources={(a,2,2,0,True) for a in range(1<<(self.size-1)) if a&3}
        reached=set(self.sources);queue=deque(self.sources);self.edges={};reverse={}
        while queue:
            u=queue.popleft();buf,oldstate,newstate,phase,first=u;out=[]
            for bit in (0,1):
                full=buf|(bit<<(self.size-1));old=full&(self.patterns-1)
                history=[full]
                for _ in range(stride):history.append(q(history[-1]))
                new=history[-1]&(self.patterns-1)
                if first and any(not a&3 for a in history):continue
                v=(full>>1,self.advance(oldstate,old&1),self.advance(newstate,new&1),1-phase,False)
                charge=sum(int((a^b)&1==0) for a,b in zip(history,history[1:])) if first else 0
                edge=(u,v,old,new,bit,charge);out.append(edge);reverse.setdefault(v,[]).append(u)
                if v not in reached:reached.add(v);queue.append(v)
            self.edges[u]=out
        self.ends={u for u in reached if u[0]==0 and u[1]==u[2]==1 and not u[4]}
        coreach=set(self.ends);queue=deque(coreach)
        while queue:
            for u in reverse.get(queue.popleft(),[]):
                if u not in coreach:coreach.add(u);queue.append(u)
        self.vertices=reached&coreach;self.sources&=self.vertices
        assert self.sources and self.ends

    @staticmethod
    def advance(state,bit):return bit*2+int(state%2 or state//2==0 and bit==0)

    def features(self,a):
        result={8*self.patterns+(a&(self.patterns-1)):1};state=2
        for k in range(a.bit_length()+self.r+3):
            code=(a>>k)&(self.patterns-1)
            if code or not state%2:add(result,(k%2*4+state)*self.patterns+code,1)
            state=self.advance(state,(a>>k)&1)
        return result

    def gain(self,edge):
        u,_,old,new,_,_=edge;_,os,ns,phase,first=u;result={}
        if old or not os%2:add(result,(phase*4+os)*self.patterns+old,-1)
        if new or not ns%2:add(result,(phase*4+ns)*self.patterns+new,1)
        if first:
            add(result,8*self.patterns+old,-1);add(result,8*self.patterns+new,1)
        return result

    def controls(self):
        rng=random.Random(2026102407);count=0
        for _ in range(10000):
            width=rng.randrange(4,130);a=rng.getrandbits(width);history=[a]
            for _ in range(self.stride):history.append(q(history[-1]))
            b=history[-1]
            if any(not x&3 for x in history):continue
            u=(a&((1<<(self.size-1))-1),2,2,0,True);assert u in self.sources
            accum={};charge=0
            for k in range(width+self.size+4):
                bit=(a>>(k+self.size-1))&1;edge,=[e for e in self.edges[u] if e[4]==bit]
                assert edge[1] in self.vertices
                for j,v in self.gain(edge).items():add(accum,j,v)
                charge+=edge[5];u=edge[1]
            assert u in self.ends and charge==sum(int((x^y)&1==0) for x,y in zip(history,history[1:]))
            expected=self.features(b)
            for j,v in self.features(a).items():add(expected,j,-v)
            expected={j:v for j,v in expected.items() if v}
            assert accum==expected
            count+=1
            if count==128:break
        assert count==128
        return {'whole_word_accounting_examples':count,'all_passed':True}

    def solve(self,seconds):
        potential={u:self.dim+i for i,u in enumerate(sorted(self.vertices))}
        rows=[];rhs=[]
        for u in self.sources:rows.append({potential[u]:-1});rhs.append(0)
        for u in self.vertices:
            for edge in self.edges[u]:
                v=edge[1]
                if v not in self.vertices:continue
                row=self.gain(edge);add(row,potential[u],1);add(row,potential[v],-1)
                reward=edge[5]
                rows.append(row);rhs.append(-reward)
        for u in self.ends:rows.append({potential[u]:1});rhs.append(0)
        data,cols,ptr=[],[],[0]
        for row in rows:
            for j,v in row.items():cols.append(j);data.append(v)
            ptr.append(len(data))
        dim=self.dim+len(potential);matrix=csr_matrix((data,cols,ptr),shape=(len(rows),dim))
        bounds=[(None,None)]*dim
        for state in range(8):
            if state%2:bounds[state*self.patterns]=(0,0)
        fit=linprog(np.zeros(dim),A_ub=matrix,b_ub=rhs,bounds=bounds,method='highs-ds',
                    options={'time_limit':seconds})
        report={'untrusted_synthesis_only':True,'Lean_verified':False,'full_problem_claim':False,
                'finite_OR_classification_proved':False,'r':self.r,'stride':self.stride,'vertices':len(potential),
                'inequalities':len(rhs),'variables':dim,'status':int(fit.status),'message':fit.message,
                'exact_LP_refutation':False,'positivity_premise_used':False}
        if fit.success:
            rational=[Fraction(float(x)).limit_denominator(100000) for x in fit.x]
            exact=all(sum(v*rational[j] for j,v in row.items())<=b for row,b in zip(rows,rhs))
            exact &= all(rational[state*self.patterns]==0 for state in range(8) if state%2)
            report.update(candidate=[str(x) for x in rational],exact_rational_inequalities_passed=exact,
                          kernel_certificate_verified=False)
        return report


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--radius',type=int,default=2)
    ap.add_argument('--stride',type=int,default=1,choices=[1,2])
    ap.add_argument('--seconds',type=float,default=30);args=ap.parse_args();began=time.monotonic()
    model=Model(args.radius,args.stride);checked=model.controls();result=model.solve(args.seconds)
    result.update(controls=checked,seconds=round(time.monotonic()-began,3))
    tag='-s2' if args.stride==2 else ''
    Path(__file__).with_name('finite-Q-OR-rank-r'+str(args.radius)+tag+'.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in result.items() if k!='candidate'}))
