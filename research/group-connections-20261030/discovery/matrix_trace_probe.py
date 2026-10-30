from pathlib import Path
from itertools import product
from collections import deque
import time,json
R=Path(__file__).resolve().parent;start=time.monotonic();CAP=120
# bit i=2*row+column
MUL=[[sum(((((a>>(2*i))&1)*((b>>j)&1))^(((a>>(2*i+1))&1)*((b>>(2+j))&1)))<<(2*i+j) for i in range(2) for j in range(2)) for b in range(16)] for a in range(16)]
I=9
assert all(MUL[I][a]==a==MUL[a][I] for a in range(16))
def trace(a):return ((a&1)^((a>>3)&1))
def edges(w,rule):
 out=[]
 for word in range(1<<(w+2)):
  new=sum(((rule>>((word>>i)&7))&1)<<i for i in range(w))
  # elementary rule index uses left*4+center*2+right, spatial low bit is left
  new=sum(((rule>>((((word>>i)&1)<<2)|(((word>>(i+1))&1)<<1)|((word>>(i+2))&1)))&1)<<i for i in range(w))
  out.append((word&((1<<(w+1))-1),word>>1,new,(word>>1)&((1<<w)-1)))
 return out

def witness(labels,w,maxn=8):
 for n in range(1,maxn+1):
  base=I
  for j in range(n):base=MUL[labels[0]][base]
  baseline=trace(base)
  for word in range(1,1<<n):
   p=I
   for j in range(n):
    block=sum(((word>>((j+k)%n))&1)<<k for k in range(w))
    p=MUL[labels[block]][p]
   if trace(p)!=baseline:return {'length':n,'word':word,'vacuum_trace':baseline,'trace':trace(p)}
 return None

def exact(labels,w,rule=30):
 E=edges(w,rule);V=1<<(w+1);out=[[] for _ in range(V)]
 for s,t,a,b in E:out[s].append((t,labels[a],labels[b]))
 for root in range(V):
  bases=[{} for _ in range(V)];q=deque()
  def put(v,x):
   y=x
   for p,z in sorted(bases[v].items(),reverse=True):
    if (y>>p)&1:y^=z
   if not y:return False
   bases[v][y.bit_length()-1]=y;q.append((v,x));return True
  put(root,I|(I<<4))
  while q:
   v,x=q.popleft()
   if v==root and ((x&153).bit_count()&1):return False
   a=x&15;b=x>>4
   for t,l,r in out[v]:put(t,MUL[l][a]|(MUL[r][b]<<4))
 return True

def finite_invariance(labels,w,rule,nmax=5):
 for n in range(1,nmax+1):
  for word in range(1<<n):
   new=sum(((rule>>((((word>>((j-1)%n))&1)<<2)|(((word>>j)&1)<<1)|((word>>((j+1)%n))&1)))&1)<<j for j in range(n))
   vals=[]
   for row in [word,new]:
    p=I
    for j in range(n):p=MUL[labels[sum(((row>>((j+k)%n))&1)<<k for k in range(w))]][p]
    vals.append(trace(p))
   if vals[0]!=vals[1]:return False
 return True
controls=[]
for rule in [204,240]:
 for labels in [(1,0),(9,3),(2,7),(0,0)]:
  assert exact(labels,1,rule) and finite_invariance(labels,1,rule)
 controls.append({'rule':rule,'all_selected_pass':True})
for labels in product(range(16),repeat=2):
 e=exact(labels,1);f=finite_invariance(labels,1,30)
 assert not e or f
controls.append({'rule':30,'width1_exact_positives_pass_finite_control':True})
results=[];positive=None
for w in [1,2]:
 tested=nonconstant=exact_positive=0;t=time.monotonic()
 for labels in product(range(16),repeat=1<<w):
  if time.monotonic()-start>CAP:break
  tested+=1
  # finite low-length failures prune before the universal test
  if not finite_invariance(labels,w,30,3):continue
  wit=witness(labels,w)
  if wit is None:continue
  nonconstant+=1
  if exact(labels,w):
   exact_positive+=1;positive={'width':w,'labels':labels,'witness':wit};break
 results.append({'width':w,'tested':tested,'total':16**(1<<w),'nonconstant_after_finite_prune':nonconstant,'exact_positive':exact_positive,'seconds':round(time.monotonic()-t,3),'complete':tested==16**(1<<w)})
 if positive or time.monotonic()-start>CAP:break
record={'controls':controls,'results':results,'positive':positive,'seconds':round(time.monotonic()-start,3),'interpretation':'Bounded representation family only. Nonconstancy search uses fixed lengths<=8; universal invariance check uses exact reachable linear spans.'}
(R/'matrix-trace-result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2),flush=True)
