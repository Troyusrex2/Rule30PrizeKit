from pathlib import Path
import json,time
R=Path(__file__).resolve().parent;S=(Path(__file__).resolve().parent/'input/PROFILE-GRAPH.json')
start=time.monotonic();graphs=json.loads(S.read_text())['graphs'];results=[]
for g in graphs:
 q=g['q']
 if q<4:continue
 mask=(1<<q)-1;points={}
 for a,b in g['nodes']:
  d=b^((b>>1)|((b&1)<<(q-1)))
  if d==mask:continue # global alternating ambiguity is already established
  for t in range(q):
   rot=((d>>t)|(d<<(q-t)))&mask
   y=(a>>t)&1
   points.setdefault((rot,y),{'a':a,'b':b,'phase':t,'derivative':d,'output':y})
 rows=[]
 for radius in range(min(15,q//2-1)+1):
  n=2*radius+1;nm=(1<<n)-1;groups={};conflicts=[]
  for (rot,y),wit in points.items():
   # leftmost bit is phase t-radius
   context=(((rot<<radius)|(rot>>(q-radius)))&mask)&nm
   if context not in groups:groups[context]=(y,wit)
   elif groups[context][0]!=y:
    conflicts.append({'context':context,'first':groups[context][1],'second':wit})
  unique={x['context']:x for x in conflicts}
  nonglobal=[x for k,x in unique.items() if k!=nm]
  rows.append({'radius':radius,'length':n,'observed_contexts':len(groups),'ambiguous_contexts':len(unique),'non_all1_ambiguous':len(nonglobal),'witness':nonglobal[0] if nonglobal else None})
  if time.monotonic()-start>30:raise TimeoutError('registered context cap')
 results.append({'q':q,'pointed_pairs':len(points),'radii':rows})
(R/'profile-context-result.json').write_text(json.dumps({'results':results,'seconds':time.monotonic()-start},indent=2)+'\n')
print(json.dumps({'graphs':[{'q':x['q'],'radii':[(r['radius'],r['non_all1_ambiguous']) for r in x['radii']]} for x in results],'seconds':time.monotonic()-start}))
