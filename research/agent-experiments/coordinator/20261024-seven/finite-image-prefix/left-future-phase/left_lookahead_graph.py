"""Finite-prefix restrictions forced by H future constrained left updates.

Enumerate legal future free words, reconstruct their unique 2H+1 left
prefix by the exact triangular inverse, and verify it by forward updates.
An eventual finite coupled counterexample obeys all these restrictions.
Short canonical words are zero padded for the prefix test, never discarded.
"""
import collections,functools,itertools
from left_zero_wall_graph import advance

FORBIDDEN=[tuple(map(int,w)) for w in ['00','11111','010110','011010','1011010','01101110','0101011110','0101110110','01101111010','0110111101110']]
def F(x):return (x>>1)^(x|(x<<1))

def allowed_word(word,r,H):
 L=sum(x<<i for i,x in enumerate(word));free=[]
 for _ in range(H):
  if not L&1:return False
  L1=F(L);b=L1&1
  if b==0 and r==0 or b==1 and r==4:return False
  r=r+1 if b else 0;free.append(b)
  if any(tuple(free[-len(w):])==w for w in FORBIDDEN):return False
  L=F(L1)
 return bool(L&1)

@functools.lru_cache(None)
def prefixes(r,H):
 words=[((),r)]
 for _ in range(H):
  new=[]
  for word,q in words:
   for b in [0,1]:
    if b==0 and q==0 or b==1 and q==4:continue
    w=word+(b,)
    if any(w[-len(p):]==p for p in FORBIDDEN):continue
    new.append((w,q+1 if b else 0))
  words=new
 allowed=set();W=2*H+1
 for free,_ in words:
  prev=[0]*(W+1);cur=[1 if t%2==0 else free[t//2] for t in range(W)];row=[]
  while cur:
   row.append(cur[0]);prev,cur=cur,[cur[j+1]^(cur[j]|prev[j]) for j in range(len(cur)-1)]
  assert len(row)==W and allowed_word(row,r,H)
  allowed.add(tuple(row))
 trie={w[:n] for w in allowed for n in range(W+1)}
 assert allowed and () in trie
 return frozenset(allowed),frozenset(trie)

def graph(T,context,H):
 assert T.shape[1]==2 and H>=1
 allowed,trie=prefixes(context,H);W=2*H+1
 initial=(0,(),0,0,());states=[initial];index={initial:0};queue=collections.deque([initial]);edges=[];terminals={}
 while queue:
  st=queue.popleft();stage,buf,p,q,hist=st;u=index[st]
  if stage and buf[-1]==1 and (hist is None or hist+(0,)*(W-len(hist)) in allowed):
   ss=stage;h=buf;r=q;tail=[]
   for _ in range(4):
    result=advance(ss,h,0)
    if result is None:break
    ss,h,y=result
    if y is not None:tail.append((r,y));r=int(T[r,y])
   else:terminals[u]=(p,r,tail)
  for x in [1] if not stage else [0,1]:
   nh=None if hist is None else hist+(x,)
   if nh is not None:
    if nh not in trie:continue
    if len(nh)==W:nh=None
   result=advance(stage,buf,x)
   if result is None:continue
   ss,h,y=result;r=q;costs=[]
   if y is not None:costs=[(q,y)];r=int(T[r,y])
   new=(ss,h,int(T[p,x]),r,nh)
   if new not in index:index[new]=len(states);states.append(new);queue.append(new)
   edges.append((u,index[new],p,x,costs))
 reverse=collections.defaultdict(list)
 for u,v,*_ in edges:reverse[v].append(u)
 live=set(terminals);queue=collections.deque(live)
 while queue:
  for u in reverse[queue.popleft()]:
   if u not in live:live.add(u);queue.append(u)
 assert 0 in live
 return states,[e for e in edges if e[0] in live and e[1] in live],{u:t for u,t in terminals.items() if u in live},live

def controls():
 import numpy as np
 checks=0
 for H in [1,2,3,4]:
  for r in range(5):
   states,edges,terminals,live=graph(np.zeros((1,2),dtype=np.int16),r,H);lookup={(u,x):v for u,v,p,x,out in edges}
   for n in range(1,11):
    for middle in itertools.product(range(2),repeat=max(0,n-2)):
     word=[1] if n==1 else [1]+list(middle)+[1];u=0
     for x in word:u=lookup.get((u,x),-1)
     assert (u in terminals)==allowed_word(word,r,H),(H,r,word)
     checks+=1
 large=0
 for H in [8,13]:
  for r in range(5):
   allowed,_=prefixes(r,H);states,edges,terminals,live=graph(np.zeros((1,2),dtype=np.int16),r,H);lookup={(u,x):v for u,v,p,x,out in edges}
   for w in sorted(allowed):
    variants=[list(w),list(w)+[1,0,1,1,0,1]]
    for i in [1,H,2*H]:
     changed=list(w);changed[i]^=1;variants.append(changed)
    for word in variants:
     while word and not word[-1]:word.pop()
     u=0
     for x in word:u=lookup.get((u,x),-1)
     assert (u in terminals)==allowed_word(word,r,H),(H,r,word)
     large+=1
 return {'canonical_finite_left_context_lookahead_language_checks':checks,'exhaustive_horizons':[1,2,3,4],'generated_valid_and_mutated_large_horizon_paths':large,'large_horizons':[8,13],'all_passed':True,'Lean_verified':False}
