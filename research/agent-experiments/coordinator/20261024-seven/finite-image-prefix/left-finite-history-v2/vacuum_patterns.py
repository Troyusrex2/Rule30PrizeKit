"""Exact prefix-union reader for all five phases of the period-five vacuum.

The free stream 01111 repeated has a spatial inverse-column cycle of 155,
after one column. Reader states retain which of its five temporal phases
still matches the entire left prefix. Both right-token choices share each
transition. It is used with the sparse-defect, bounded-below rank model;
no learned pattern or bounded simulation is promoted to a CA theorem.
"""
import argparse,collections,hashlib,json,random,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from core import save

def vacua():
 result=[];f=[0,1,1,1,1]
 for r in range(5):
  start=(r+1)%5;free=f[start:]+f[:start];A=sum((1 if t%2==0 else free[t//2])<<t for t in range(10));B=0;seen={};columns=[]
  while (A,B) not in seen:
   assert len(columns)<10000;seen[A,B]=len(columns);columns.append(A);A,B=(((A>>1)|((A&1)<<9))^(A|B))&1023,A
  mu=seen[A,B];period=len(columns)-mu;assert mu==1 and period==155
  result.append({'context':r,'free_period':free,'transient':mu,'period':period,'columns':columns,'left_bits':[x&1 for x in columns]})
 return result

def reader(patterns):
 initial=tuple((r,0) for r in range(5));states=[None,initial];index={initial:1};rows=[[1]*4];queue=collections.deque([initial])
 while queue:
  st=queue.popleft();row=[]
  for x in range(4):
   new=[]
   for r,pos in st:
    p=patterns[r]
    if p['left_bits'][pos]!=(x&1):continue
    nxt=pos+1 if pos+1<len(p['left_bits']) else p['transient'];new.append((r,nxt))
   new=tuple(new)
   if new not in index:index[new]=len(states);states.append(new);queue.append(new)
   row.append(index[new])
  rows.append(row)
 assert len(rows)==len(states)
 return np.array(rows,dtype=np.int16),states,index[()]

def controls(patterns,T,states,sink):
 cells=prefixes=0;rng=random.Random(302561)
 def bit(r,j):
  p=patterns[r];a=p['left_bits'];mu=p['transient'];return a[j if j<len(a) else mu+(j-mu)%p['period']]
 for r,p in enumerate(patterns):
  previous=[0]*513;current=[1 if t%2==0 else p['free_period'][t//2%5] for t in range(512)];literal=[]
  for d in range(512):
   literal.append(current[0]);previous,current=current,[current[i+1]^(current[i]|previous[i]) for i in range(len(current)-1)]
  assert literal==[bit(r,j) for j in range(512)];cells+=512
  L=sum(x<<j for j,x in enumerate(literal));free=1-((L>>1)&1);assert free==p['free_period'][0];future=0 if free==0 else r+1
  L1=(L>>1)^(L|(L<<1)|1);L2=(L1>>1)^(L1|(L1<<1));assert [L2>>j&1 for j in range(508)]==[bit(future,j) for j in range(508)];cells+=508
  for flip in [-1,1,7,53,151,300]:
   q=int(T[0,3]);history=[]
   for j in range(400):
    value=bit(r,j)^int(j==flip);history.append(value);q=int(T[q,value+2*rng.randrange(2)])
    expected=[]
    for s in range(5):
     if all(bit(s,i)==v for i,v in enumerate(history)):
      p2=patterns[s];n=len(history);expected.append((s,n if n<len(p2['left_bits']) else p2['transient']+(n-p2['transient'])%p2['period']))
    assert states[q]==tuple(expected);prefixes+=1
 return {'independent_scalar_triangle_and_physical_left_bits':cells,'independent_entire_prefix_language_checks':prefixes,'vacuum_period':155,'vacuum_transient':1,'reader_states':len(T),'absorbing_reject_state':sink,'all_passed':True,'Lean_verified':False}

