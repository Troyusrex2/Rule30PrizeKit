"""Split an exact finite-past graph by upcoming free bits used by its energy.

The score phase is (preceding-one count, next K free bits). Its successor
uses the shifted K-bit window. Group physical predecessor prefixes by the
next K+1 bits, then intersect the existing deterministic graph language.
No input, output, moving-front, or short-word semantics are changed.
"""
import collections,functools
from left_finite_history_graph import graph as base_graph,prefixes
from left_lookahead_graph import F

def future_word(word,K):
 x=sum(b<<i for i,b in enumerate(word));out=[]
 for _ in range(K):out.append(F(x)&1);x=F(F(x))
 return tuple(out)

@functools.lru_cache(None)
def groups(r,b,H,K,depth):
 assert 1<=K<H
 result=collections.defaultdict(set)
 for predecessor in prefixes(r,b,H,depth)[0]:
  current=sum(x<<i for i,x in enumerate(predecessor))
  for _ in range(depth):current=F(F(current))
  w=future_word(tuple(current>>i&1 for i in range(2*H+1)),K+1)
  assert w[0]==b;result[w].add(predecessor)
 return {w:frozenset(values) for w,values in result.items()}

def intersect(data,allowed):
 states,edges,terminals,live=data;W=len(next(iter(allowed)));trie={w[:i] for w in allowed for i in range(W+1)}
 kept=[];successors=collections.defaultdict(list);reverse=collections.defaultdict(list)
 for e in edges:
  u,v,cur,aft=e;hist=states[u][-1];x=states[v][0][0][1][-1]
  if hist is not None and hist+(x,) not in trie:continue
  kept.append(e);successors[u].append(v);reverse[v].append(u)
 reach={0};queue=collections.deque([0])
 while queue:
  for v in successors[queue.popleft()]:
   if v not in reach:reach.add(v);queue.append(v)
 ends={u:t for u,t in terminals.items() if u in reach and (states[u][-1] is None or states[u][-1]+(0,)*(W-len(states[u][-1])) in allowed)}
 live=set(ends);queue=collections.deque(live)
 while queue:
  for u in reverse[queue.popleft()]:
   if u in reach and u not in live:live.add(u);queue.append(u)
 if 0 not in live:return None
 return states,[e for e in kept if e[0] in live and e[1] in live],ends,live

def branches(T,H,K,depth):
 for r in range(5):
  for b in range(2):
   if b==0 and r==0 or b==1 and r==4:continue
   base=base_graph(T,r,b,H,depth)
   for word,allowed in sorted(groups(r,b,H,K,depth).items()):
    data=intersect(base,allowed)
    if data is not None:yield (r,word[:K]),(r+1 if b else 0,word[1:]),0 if b else 4-r,data
