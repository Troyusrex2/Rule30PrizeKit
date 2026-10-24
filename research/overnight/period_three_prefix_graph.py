"""Whole-word graph synthesis for C3w(011); numerical output is not a proof.

The graph reads any finite initial row followed by zeros, computing its exact
three-step image with boundary 010. Both rows' first three cells must be
uniform. It tracks each row's first disagreement with its appropriate
period-three ether reference. A successful score still requires kernel
verification; an unsuccessful LP is not an exact impossibility theorem.
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

from period_three_prefix_rank_probe import BASE, Model as FiniteModel, cycle, good, controls
from stripe_prefix_dfa_potential import add


class Model:
    def __init__(self,r,restrict_front=False):
        assert 1<=r<=4
        self.r=r;self.size=r+6;self.patterns=1<<r;self.restrict_front=restrict_front
        self.states=48;self.dim=self.states*self.patterns+2
        self.sources=set()
        for a in range(1<<(r+2)):
            if a&7 not in (0,7):continue
            for newmode in (0,1):
                self.sources.add((a<<3,24*(a&1)+1,24*newmode+1,0))
        reached=set(self.sources);queue=deque(self.sources)
        self.edges={};reverse={}
        while queue:
            u=queue.popleft();buf,oldstate,newstate,depth=u
            out=[]
            for bit in (0,1):
                full=buf | (bit<<(self.size-1))
                old=(full>>3)&(self.patterns-1)
                new=self.output(full,depth)
                oldmode=oldstate//24;newmode=newstate//24
                if depth<3 and (old&1!=oldmode or new&1!=newmode):continue
                if restrict_front and (not self.valid_front(oldstate,old&1) or
                                       not self.valid_front(newstate,new&1)):continue
                v=(full>>1,self.advance(oldstate,old&1),self.advance(newstate,new&1),min(3,depth+1))
                edge=(u,v,old,new,bit,depth==0)
                out.append(edge);reverse.setdefault(v,[]).append(u)
                if v not in reached:reached.add(v);queue.append(v)
            self.edges[u]=out
        self.ends={u for u in reached if u[0]==0 and u[3]==3 and u[1]%2==u[2]%2==0}
        coreach=set(self.ends);queue=deque(coreach)
        while queue:
            for u in reverse.get(queue.popleft(),[]):
                if u not in coreach:coreach.add(u);queue.append(u)
        self.vertices=reached&coreach;self.sources&=self.vertices
        assert self.sources and self.ends

    def output(self,full,depth):
        # The buffer's origin is depth-3, with depth saturated at 3 after the
        # physical boundary no longer affects the local three-step window.
        cells=[(full>>j)&1 for j in range(self.size)]
        origin=depth-3
        for boundary in (1,0,0):
            new=[]
            for j in range(1,len(cells)-1):
                pos=origin+j
                new.append((boundary if pos==-1 else 0) if pos<0 else
                           cells[j+1]^(cells[j]|cells[j-1]))
            cells=new;origin+=1
        return sum(bit<<j for j,bit in enumerate(cells))

    @staticmethod
    def advance(state,bit):
        mode,tail=divmod(state,24);phase,matched=divmod(tail,2)
        return mode*24+((phase+1)%12)*2+int(bool(matched) and bit==BASE[mode][phase])

    @staticmethod
    def valid_front(state,bit):
        mode,tail=divmod(state,24);phase,matched=divmod(tail,2)
        return not matched or bit==BASE[mode][phase] or phase%3==0

    @staticmethod
    def admissible(a):
        mode=a&1
        for i in range(a.bit_length()+12):
            if (a>>i)&1!=BASE[mode][i%12]:return i%3==0
        raise AssertionError('A finite row must differ from its infinite reference')

    def index(self,state,pattern):return state*self.patterns+pattern

    def gain(self,edge,old_only=False):
        u,_,old,new,_,first=edge
        result={}
        if old or u[1]%2:add(result,self.index(u[1],old),-1)
        if not old_only and (new or u[2]%2):add(result,self.index(u[2],new),1)
        if first:
            add(result,self.dim-2,-1 if old_only else 0)
            add(result,self.dim-1,-(old&1))
            if not old_only:add(result,self.dim-1,new&1)
        return result

    def controls(self):
        rng=random.Random(2026102406);finite=FiniteModel(self.r,12,True)
        accepted=0
        for _ in range(100000):
            width=rng.randrange(6,130)
            a=rng.getrandbits(width);b=cycle(a)
            if not good(a) or not good(b):continue
            if self.restrict_front and (not self.admissible(a) or not self.admissible(b)):continue
            u=((a&((1<<(self.r+2))-1))<<3,24*(a&1)+1,24*(b&1)+1,0)
            assert u in self.sources
            accum={};flip=0
            for k in range(width+self.size+18):
                bit=(a>>(k+self.r+2))&1
                edge,=[e for e in self.edges[u] if e[4]==bit]
                assert edge[1] in self.vertices
                assert edge[2]==(a>>k)&(self.patterns-1)
                assert edge[3]==(b>>k)&(self.patterns-1)
                for j,v in self.gain(edge).items():add(accum,j,v)
                flip+=int(edge[5] and (edge[2]^edge[3])&1)
                u=edge[1]
            assert u in self.ends and flip==((a^b)&1)
            expected=finite.features(b)
            for j,v in finite.features(a).items():add(expected,j,-v)
            expected={j:v for j,v in expected.items() if v}
            assert accum==expected
            accepted+=1
            if accepted==128:break
        assert accepted==128
        return {'exact_three_step_word_controls':accepted,'feature_accounting_passed':True,
                'arbitrary_length_graph_coverage_is_not_Lean_verified':True}

    def solve(self,reward,seconds):
        rv={u:self.dim+i for i,u in enumerate(sorted(self.vertices))}
        offset=self.dim+len(rv);qv={u:offset+i for i,u in enumerate(sorted(self.vertices))}
        dim=offset+len(qv);rows=[];rhs=[]
        def constraint(cost,u,v,potential,charge=0):
            row=dict(cost);add(row,potential[u],1);add(row,potential[v],-1)
            rows.append(row);rhs.append(-charge)
        for s in self.sources:
            rows.append({rv[s]:-1});rhs.append(0)
            rows.append({qv[s]:-1});rhs.append(0)
        for u in self.vertices:
            for edge in self.edges[u]:
                v=edge[1]
                if v not in self.vertices:continue
                charge=int(edge[5])
                if reward=='flip':charge*=int((edge[2]^edge[3])&1)
                constraint(self.gain(edge),u,v,rv,charge)
                constraint(self.gain(edge,old_only=True),u,v,qv)
        for e in self.ends:
            rows.append({rv[e]:1});rhs.append(0)
            rows.append({qv[e]:1});rhs.append(0)
        values,cols,ptr=[],[],[0]
        for row in rows:
            for j,v in row.items():cols.append(j);values.append(v)
            ptr.append(len(values))
        matrix=csr_matrix((values,cols,ptr),shape=(len(rows),dim),dtype=float)
        bounds=[(None,None)]*dim
        for state in range(self.states):
            if state%2==0:bounds[self.index(state,0)]=(0,0)
        result=linprog(np.zeros(dim),A_ub=matrix,b_ub=rhs,bounds=bounds,
                       method='highs-ds',options={'time_limit':seconds})
        report={'untrusted_synthesis_only':True,'Lean_verified':False,'full_problem_claim':False,
                'C3w_011_proved':False,'r':self.r,'reward':reward,'graph_vertices':len(rv),
                'first_reference_defect_at_multiple_of_three':self.restrict_front,
                'graph_edges':sum(len(self.edges[u]) for u in self.vertices),'variables':dim,
                'inequalities':len(rhs),'status':int(result.status),'message':result.message,
                'exact_LP_refutation':False,'candidate_is_verified_rank':False}
        if result.success:
            rational=[Fraction(float(x)).limit_denominator(100000) for x in result.x]
            exact=all(sum(v*rational[j] for j,v in row.items())<=b for row,b in zip(rows,rhs))
            exact &= all(rational[self.index(s,0)]==0 for s in range(self.states) if s%2==0)
            report.update(candidate=[str(x) for x in rational],exact_rational_inequalities_passed=exact,
                          kernel_certificate_verified=False)
        return report


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',type=int,default=2)
    ap.add_argument('--reward',choices=['every','flip'],default='flip')
    ap.add_argument('--seconds',type=float,default=30)
    ap.add_argument('--restrict-front',action='store_true')
    args=ap.parse_args();began=time.monotonic()
    controls();model=Model(args.radius,args.restrict_front);checked=model.controls()
    print(json.dumps({'graph_vertices':len(model.vertices),'controls':checked}),flush=True)
    result=model.solve(args.reward,args.seconds);result.update(controls=checked,seconds=round(time.monotonic()-began,3))
    tag='-front' if args.restrict_front else ''
    path=Path(__file__).with_name('period-three-prefix-graph-r'+str(args.radius)+'-'+args.reward+tag+'.json')
    path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in result.items() if k!='candidate'}))


if __name__=='__main__':main()
