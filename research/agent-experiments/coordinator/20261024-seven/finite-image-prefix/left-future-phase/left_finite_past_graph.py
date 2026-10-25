"""Require an explicit finite predecessor, rather than only a past label.

Stream a canonical predecessor P, emit current=G(P) after delay2, then
after=G(current) after delay4. Both heads are black. Eight zero inputs
flush both moving fronts; score current only through its own fourth flush.
This witnesses finite past by construction and prevents Garden rows from
being paired with an impossible prior free-bit context.
"""
import collections,functools
from left_zero_wall_graph import advance,two
from left_lookahead_graph import prefixes as current_prefixes,F,allowed_word

def decode_prefix(word,past_free):
 buf=(1,0,1,1-past_free);old=[1,1-past_free]
 for y in word:
  x=y^two(list(reversed(buf+(0,))));old.append(x);buf=buf[1:]+(x,)
 return tuple(old)

@functools.lru_cache(None)
def prefixes(context,free,H):
 assert not(free==0 and context==0 or free==1 and context==4)
 past_free=int(context>0);allowed=set()
 for cur in current_prefixes(context,H)[0]:
  if 1-cur[1]!=free:continue
  old=decode_prefix(cur,past_free);x=sum(b<<i for i,b in enumerate(old));after=F(F(x))
  assert tuple(after>>i&1 for i in range(len(cur)))==cur and (F(x)&1)==past_free
  allowed.add(old)
 W=2*H+3;assert allowed and all(len(w)==W for w in allowed)
 return frozenset(allowed),frozenset(w[:n] for w in allowed for n in range(W+1))

def step(sa,ba,sb,bb,x):
 a=advance(sa,ba,x)
 if a is None:return None
 sa,ba,y=a;z=None
 if y is not None:
  b=advance(sb,bb,y)
  if b is None:return None
  sb,bb,z=b
 return sa,ba,sb,bb,y,z

def outputs(word):
 sa=sb=0;ba=bb=();cur=[];aft=[]
 for x in word:
  result=step(sa,ba,sb,bb,x)
  if result is None:return None
  sa,ba,sb,bb,y,z=result
  if y is not None:cur.append(y)
  if z is not None:aft.append(z)
 for j in range(8):
  result=step(sa,ba,sb,bb,0)
  if result is None:return None
  sa,ba,sb,bb,y,z=result
  if y is not None:
   if j<4:cur.append(y)
   else:assert y==0
  if z is not None:aft.append(z)
 return cur,aft

def graph(T,context,free,H):
 allowed,trie=prefixes(context,free,H);W=2*H+3
 initial=(0,(),0,(),0,0,());states=[initial];index={initial:0};queue=collections.deque([initial]);edges=[];terminals={}
 while queue:
  st=queue.popleft();sa,ba,sb,bb,p,q,hist=st;u=index[st]
  if sa and ba[-1]==1 and (hist is None or hist+(0,)*(W-len(hist)) in allowed):
   aa,ab,bs,bc=sa,ba,sb,bb;pp,qq=p,q;ct=[];at=[]
   for j in range(8):
    result=step(aa,ab,bs,bc,0)
    if result is None:break
    aa,ab,bs,bc,y,z=result
    if y is not None:
     if j<4:ct.append((pp,y));pp=int(T[pp,y])
     else:assert y==0
    if z is not None:at.append((qq,z));qq=int(T[qq,z])
   else:terminals[u]=(pp,qq,ct,at)
  for x in [1] if not sa else [0,1]:
   nh=None if hist is None else hist+(x,)
   if nh is not None:
    if nh not in trie:continue
    if len(nh)==W:nh=None
   result=step(sa,ba,sb,bb,x)
   if result is None:continue
   aa,ab,bs,bc,y,z=result;pp,qq=p,q;ct=[];at=[]
   if y is not None:ct=[(pp,y)];pp=int(T[pp,y])
   if z is not None:at=[(qq,z)];qq=int(T[qq,z])
   new=(aa,ab,bs,bc,pp,qq,nh)
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
