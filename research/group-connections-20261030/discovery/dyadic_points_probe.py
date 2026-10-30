from pathlib import Path
import numpy as np,json,time
R=Path(__file__).resolve().parent;start=time.monotonic();records=[];counter=None
for N in range(17,25):
 mask=np.uint64((1<<N)-1);counts={8:0,16:0,32:0};done=0;t0=time.monotonic()
 for lo in range(0,1<<N,1<<18):
  orig=np.arange(lo,min(lo+(1<<18),1<<N),dtype=np.uint64);x=orig.copy();f8=f16=None
  for k in range(1,33):
   a=((x<<np.uint64(1))|(x>>np.uint64(N-1)))&mask
   b=((x<<np.uint64(2))|(x>>np.uint64(N-2)))&mask
   x=x^(a|b)
   if k in counts:
    fixed=x==orig;counts[k]+=int(np.count_nonzero(fixed))
    if k==8:f8=fixed
    else:
     prev=f8 if k==16 else f16
     novel=np.flatnonzero(fixed & ~prev)
     if novel.size:
      witness=int(orig[novel[0]]);counter={'ring':N,'temporal_period':k,'seed':witness};break
     if k==16:f16=fixed
  done+=len(orig)
  if counter or time.monotonic()-start>60:break
 records.append({'ring':N,'states':done,'total':1<<N,'fixed_counts':counts,'complete':done==1<<N and counter is None,'seconds':round(time.monotonic()-t0,3)})
 print(records[-1],flush=True)
 if counter or time.monotonic()-start>60:break
record={'records':records,'counterexample':counter,'seconds':time.monotonic()-start,'status':'counterexample' if counter else ('complete_bounded_test' if records[-1]['ring']==24 and records[-1]['complete'] else 'time_cap_partial')}
(R/'dyadic-periodic-points-result.json').write_text(json.dumps(record,indent=2)+'\n')
print('status',record['status'],'counter',counter,'seconds',round(record['seconds'],3),flush=True)
