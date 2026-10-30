from pathlib import Path
from collections import deque,defaultdict
import json,time
R=Path(__file__).resolve().parent;start=time.monotonic();records=[]
def period(v,q):
 p=1
 while p<=q:
  mask=(1<<q)-1
  if (((v>>p)|(v<<(q-p)))&mask)==v:return p
  p*=2
 raise AssertionError
for q in [2,4,8]:
 size=1<<q;mask=size-1;N=size*size;adj=[[] for _ in range(N)];rev=[[] for _ in range(N)]
 for a in range(size):
  for b in range(size):
   f=a|b
   if f.bit_count()%2:continue
   u=f;s=1
   while s<q:u^=u<<s;s*=2
   c=(u<<1)&mask;i=a*size+b
   for cc in [c,c^mask]:j=b*size+cc;adj[i].append(j);rev[j].append(i)
 indeg=list(map(len,rev));outdeg=list(map(len,adj));alive=bytearray([1])*N;todo=deque(i for i in range(N) if not indeg[i])
 while todo:
  i=todo.popleft()
  if not alive[i]:continue
  alive[i]=0
  for j in adj[i]:
   indeg[j]-=1
   if alive[j] and not indeg[j]:todo.append(j)
  for j in rev[i]:
   outdeg[j]-=1
   # Future extension is deliberately not required.
 pred=defaultdict(set);drop=None
 for i in range(N):
  if not alive[i]:continue
  a,b=divmod(i,size);pred[b].add(a)
  if drop is None and period(a,q)>period(b,q) and period(a,q)>2:drop={'a':a,'b':b,'period_a':period(a,q),'period_b':period(b,q),'node':i}
 ambiguous=next(({'b':b,'predecessors':sorted(v),'period_b':period(b,q)} for b,v in pred.items() if period(b,q)>2 and len(v)>1),None)
 witness=None
 if drop:
  def walk(backward):
   here=drop['node'];seen={};path=[]
   while here not in seen:
    seen[here]=len(path);path.append(divmod(here,size));here=next(j for j in (rev[here] if backward else adj[here]) if alive[j])
   return {'path':path,'cycle_starts_at':seen[here]}
  witness={'left':walk(True),'right':None}
 records.append({'q':q,'all_pairs':N,'infinite_past_core':sum(alive),'nonunique_predecessor':ambiguous,'period_drop':drop,'witness':witness})
 if time.monotonic()-start>30:raise TimeoutError
(R/'left-profile-core-result.json').write_text(json.dumps({'records':records,'seconds':time.monotonic()-start},indent=2)+'\n')
print(json.dumps({'records':[{k:v for k,v in x.items() if k!='witness'} for x in records],'seconds':time.monotonic()-start}))
