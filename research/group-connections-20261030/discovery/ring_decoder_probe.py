from pathlib import Path
import json,time
R=Path(__file__).resolve().parent;start=time.monotonic();known={};counts=[];counter=None

def rot(w,k,n):return ((w>>k)|(w<<(n-k)))&((1<<n)-1)
def period(w,q):
 p=1
 while p<=q:
  if rot(w,p,q)==w:return p
  p*=2
 raise AssertionError
for N in range(1,17):
 mask=(1<<N)-1
 def step(x):
  a=((x<<1)|(x>>(N-1)))&mask
  b=((a<<1)|(a>>(N-1)))&mask
  return x^(a|b)
 if N<=7:
  for x in range(1<<N):
   direct=sum((((x>>j)&1)^(((x>>((j-1)%N))&1)|((x>>((j-2)%N))&1)))<<j for j in range(N))
   assert step(x)==direct
 seen=bytearray(1<<N);cycles=kept=0
 for seed in range(1<<N):
  if seen[seed]:continue
  path=[];local={};x=seed
  while not seen[x]:
   local[x]=len(path);path.append(x);seen[x]=1;x=step(x)
  if x not in local:continue
  row=path[local[x]:];q=len(row);cycles+=1
  if q&(q-1) or q>256:continue
  kept+=1
  profiles=[sum(((x>>j)&1)<<t for t,x in enumerate(row)) for j in range(N)]
  for j,b in enumerate(profiles):
   a=profiles[(j-1)%N];p=period(b,q);pa=period(a,q)
   if p<=2:continue
   if pa>p:
    counter={'kind':'period_drop_to_nonalt','N':N,'seed':row[0],'q':q,'j':j,'a':a,'b':b,'period_a':pa,'period_b':p};break
   b&=(1<<p)-1;a&=(1<<p)-1
   bc,r=min((rot(b,k,p),k) for k in range(p));ac=rot(a,r,p);key=(p,bc)
   if key in known and known[key]['a']!=ac:
    counter={'kind':'nonunique_predecessor','first':known[key],'second':{'N':N,'seed':row[0],'q':q,'j':j,'rotation':r,'a':ac,'b':bc,'p':p}};break
   known.setdefault(key,{'N':N,'seed':row[0],'q':q,'j':j,'rotation':r,'a':ac,'b':bc,'p':p})
  if counter:break
  if time.monotonic()-start>45:raise TimeoutError('registered45s')
 counts.append({'ring':N,'cycles':cycles,'dyadic_cycles':kept,'complete':counter is None})
 if counter:break
(R/'ring-decoder-result.json').write_text(json.dumps({'counts':counts,'counterexample':counter,'phase_classes':len(known),'seconds':time.monotonic()-start},indent=2)+'\n')
print(json.dumps({'counts':counts,'counterexample':counter,'phase_classes':len(known),'seconds':time.monotonic()-start}))
