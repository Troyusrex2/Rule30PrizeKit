"""Test the whole nonnegative-prefix-cost rank family on exact actual examples.

A positive-reward cycle through transition and same-phase prefix inequalities
rules out every prefix-monotone energy, irrespective of finite-state or neural
implementation. No cycle means only that these finite constraints are feasible.
"""
import collections,json,random,time
from core import save
from regular_prefix_bothzero_rank_terminal import trajectory

def audit(edges):
 keys={};words=[]
 def node(word,phase):
  key=(phase,tuple(word))
  if key not in keys:keys[key]=len(words);words.append(key)
  return keys[key]
 raw=[]
 for e in edges:raw.append((node(e[0],e[2]),node(e[1],e[3]),e[4],{'kind':'actual_transition',**e[5]}))
 lengths=sorted({len(w) for phase,w in words});prefixes=0
 for u,(phase,w) in enumerate(words):
  for n in reversed(lengths):
   if n>=len(w):continue
   v=keys.get((phase,w[:n]))
   if v is not None:raw.append((u,v,0,{'kind':'same_phase_prefix','short_length':n,'long_length':len(w),'phase':phase}));prefixes+=1;break
 n=len(words);adj=[[] for _ in range(n)];rev=[[] for _ in range(n)]
 for i,(u,v,z,m) in enumerate(raw):adj[u].append((v,i));rev[v].append((u,i))
 seen=set();order=[]
 for root in range(n):
  if root in seen:continue
  seen.add(root);stack=[(root,0)]
  while stack:
   u,pos=stack[-1]
   if pos<len(adj[u]):
    stack[-1]=(u,pos+1);v,_=adj[u][pos]
    if v not in seen:seen.add(v);stack.append((v,0))
   else:order.append(u);stack.pop()
 comp=[-1]*n;cc=0
 for root in reversed(order):
  if comp[root]!=-1:continue
  comp[root]=cc;stack=[root]
  while stack:
   u=stack.pop()
   for v,i in rev[u]:
    if comp[v]==-1:comp[v]=cc;stack.append(v)
  cc+=1
 witness=None
 for eid,(u,v,z,m) in enumerate(raw):
  if z and comp[u]==comp[v]:
   queue=collections.deque([v]);parent={v:None}
   while queue and u not in parent:
    at=queue.popleft()
    for nxt,k in adj[at]:
     if comp[nxt]==comp[u] and nxt not in parent:parent[nxt]=(at,k);queue.append(nxt)
   path=[];at=u
   while at!=v:old,k=parent[at];path.append(k);at=old
   sequence=[eid]+list(reversed(path));witness=[]
   for k in sequence:
    a,b,c,meta=raw[k];witness.append({'before_phase':words[a][0],'after_phase':words[b][0],'before_word':list(words[a][1]),'after_word':list(words[b][1]),'reward':c,'evidence':meta})
   break
 return {'vertices':n,'transition_constraints':len(edges),'prefix_constraints':prefixes,'components':cc,'positive_cycle':witness,'all_constraints_possible_if_no_positive_cycle':witness is None}

def main():
 start=time.monotonic();rng=random.Random(302521);structured=[0,1,2,3,5,17,31,495]+[1<<k for k in [2,3,7,15,31,63]]+[(1<<k)-1 for k in [2,3,7,15,31,63]]
 initials=structured+[rng.getrandbits(rng.randrange(8,129)) for _ in range(48)]
 train=[e for R in initials for e in trajectory(R,128,6)];held=[e for R in [0,1,2,31,495]+[rng.getrandbits(256) for _ in range(8)] for e in trajectory(R,512,256)]
 a=audit(train);b=audit(train+held);out={'training':a,'training_and_heldout':b,'exact_discrete_graph_computation':True,'actual_right_traces':True,'Lean_verified':False,'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)}
 save('prefix-monotone-rank-audit.json',out)
 print({'train_vertices':a['vertices'],'train_prefix_edges':a['prefix_constraints'],'train_positive_cycle':None if a['positive_cycle'] is None else len(a['positive_cycle']),'combined_prefix_edges':b['prefix_constraints'],'combined_positive_cycle':None if b['positive_cycle'] is None else len(b['positive_cycle']),'seconds':out['seconds']},flush=True)
if __name__=='__main__':main()
