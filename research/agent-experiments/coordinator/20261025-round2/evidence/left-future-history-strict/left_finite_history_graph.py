"""Exact finite history of arbitrary specified depth, with full moving fronts.

Stream P through depth+1 composed white-wall double-step transducers.
The two scored words are G^depth(P) and G^(depth+1)(P). All intermediate
heads must be black. Prefix restrictions retain a legal past phase history
and the selected forward horizon, rather than inventing a prior label.
"""
import collections,functools
from left_zero_wall_graph import advance
from left_finite_past_graph import decode_prefix
from left_lookahead_graph import prefixes as current_prefixes,F

@functools.lru_cache(None)
def histories(context,depth):
 words=[((),r) for r in range(5)]
 for _ in range(depth):
  words=[(w+(b,),r+1 if b else 0) for w,r in words for b in range(2) if not(b==0 and r==0 or b==1 and r==4)]
 return frozenset(w for w,r in words if r==context)

@functools.lru_cache(None)
def prefixes(context,free,H,depth):
 assert depth>=1 and H>=1 and not(free==0 and context==0 or free==1 and context==4)
 allowed=set()
 for cur in current_prefixes(context,H)[0]:
  if 1-cur[1]!=free:continue
  for history in histories(context,depth):
   word=cur
   for b in reversed(history):word=decode_prefix(word,b)
   x=sum(b<<i for i,b in enumerate(word))
   for b in history:
    assert x&1 and F(x)&1==b;x=F(F(x))
   assert tuple(x>>i&1 for i in range(len(cur)))==cur
   allowed.add(word)
 W=2*H+1+2*depth
 assert allowed and all(len(w)==W for w in allowed)
 return frozenset(allowed),frozenset(w[:n] for w in allowed for n in range(W+1))

def advance_chain(chain,x):
 new=[];emissions=[]
 for stage,buf in chain:
  if x is None:new.append((stage,buf));emissions.append(None);continue
  result=advance(stage,buf,x)
  if result is None:return None
  stage,buf,x=result;new.append((stage,buf));emissions.append(x)
 return tuple(new),emissions

def outputs(word,depth):
 chain=tuple((0,()) for _ in range(depth+1));cur=[];aft=[]
 for x in word:
  result=advance_chain(chain,x)
  if result is None:return None
  chain,emissions=result;y,z=emissions[-2:]
  if y is not None:cur.append(y)
  if z is not None:aft.append(z)
 for j in range(4*(depth+1)):
  result=advance_chain(chain,0)
  if result is None:return None
  chain,emissions=result;y,z=emissions[-2:]
  if y is not None:
   if j<4*depth:cur.append(y)
   else:assert y==0
  if z is not None:aft.append(z)
 return cur,aft

def graph(T,context,free,H,depth):
 allowed,trie=prefixes(context,free,H,depth);W=2*H+1+2*depth
 initial=(tuple((0,()) for _ in range(depth+1)),0,0,());states=[initial];index={initial:0};queue=collections.deque([initial]);edges=[];terminals={}
 while queue:
  st=queue.popleft();chain,p,q,hist=st;u=index[st];stage,buf=chain[0]
  if stage and buf[-1]==1 and (hist is None or hist+(0,)*(W-len(hist)) in allowed):
   newchain=chain;pp,qq=p,q;ct=[];at=[]
   for j in range(4*(depth+1)):
    result=advance_chain(newchain,0)
    if result is None:break
    newchain,emissions=result;y,z=emissions[-2:]
    if y is not None:
     if j<4*depth:ct.append((pp,y));pp=int(T[pp,y])
     else:assert y==0
    if z is not None:at.append((qq,z));qq=int(T[qq,z])
   else:terminals[u]=(pp,qq,ct,at)
  for x in [1] if not stage else [0,1]:
   nh=None if hist is None else hist+(x,)
   if nh is not None:
    if nh not in trie:continue
    if len(nh)==W:nh=None
   result=advance_chain(chain,x)
   if result is None:continue
   newchain,emissions=result;y,z=emissions[-2:];pp,qq=p,q;ct=[];at=[]
   if y is not None:ct=[(pp,y)];pp=int(T[pp,y])
   if z is not None:at=[(qq,z)];qq=int(T[qq,z])
   new=(newchain,pp,qq,nh)
   if new not in index:index[new]=len(states);states.append(new);queue.append(new)
   edges.append((u,index[new],ct,at))
 reverse=collections.defaultdict(list)
 for u,v,*_ in edges:reverse[v].append(u)
 live=set(terminals);queue=collections.deque(live)
 while queue:
  for u in reverse[queue.popleft()]:
   if u not in live:live.add(u);queue.append(u)
 assert 0 in live
 return states,[e for e in edges if e[0] in live and e[1] in live],{u:t for u,t in terminals.items() if u in live},live
