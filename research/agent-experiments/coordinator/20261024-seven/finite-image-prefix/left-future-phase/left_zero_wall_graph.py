"""Exact binary transducer on finite left rows with a forced white wall.

Input is a1..am, a1=am=1. Two physical updates with wall0 give an output
of length m+2. Accept only output a1=1 as well. In a hypothetical infinite
alternating coupled path this extra lookahead is mandatory. While the
left head is black, the alternating center's black value is masked by OR,
so the left updates agree with the white-wall subsystem (official kit).
"""
import collections
from universal_folded_row_rank import two

def advance(stage,buf,x):
 if stage==0:
  if x!=1:return None
  return 1,(1,0,1),None
 if stage==1:return 2,buf+(x,),None
 out=two(list(reversed(buf+(x,))))
 if stage==2 and out!=1:return None
 return 3,(buf+(x,))[1:],out

def updated(word):
 stage=0;buf=();out=[]
 for x in list(word)+[0]*4:
  result=advance(stage,buf,x)
  if result is None:return None
  stage,buf,y=result
  if y is not None:out.append(y)
 return out

def graph(T):
 assert T.shape[1]==2
 initial=(0,(),0,0);states=[initial];index={initial:0};queue=collections.deque([initial]);edges=[];terminals={}
 while queue:
  st=queue.popleft();stage,buf,p,q=st;u=index[st]
  if stage and buf[-1]==1:
   ss=stage;h=buf;r=q;tail=[]
   for _ in range(4):
    result=advance(ss,h,0)
    if result is None:break
    ss,h,y=result
    if y is not None:tail.append((r,y));r=int(T[r,y])
   else:terminals[u]=(p,r,tail)
  for x in [1] if not stage else [0,1]:
   result=advance(stage,buf,x)
   if result is None:continue
   ss,h,y=result;r=q;costs=[]
   if y is not None:costs=[(q,y)];r=int(T[q,y])
   new=(ss,h,int(T[p,x]),r)
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
