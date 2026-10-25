"""Stress a new exact greedy-front representation; finite experiments only."""
from pathlib import Path
from collections import Counter
import hashlib,json,random,time
root=Path(__file__).resolve().parent
start=time.monotonic()
def phi(a):return a^((a<<1)|(a<<2))
def physical(a):
    return {x for x in range(min(a)-1,max(a)+2)
            if int(x-1 in a)^(int(x in a)|int(x+1 in a))}
def lowbit(a):return (a&-a).bit_length()-1

# Independent selected-parent labels and exact mask recurrence at small sizes.
physical_rows=[{0}]
for _ in range(8):physical_rows.append(physical(physical_rows[-1]))
checks=0
for T in range(4):
    for P in range(1,5):
        a=physical_rows[T];b=physical_rows[T+P];labels={x:x for x in a^b};r=min(labels)
        packed_a=sum(1<<(T+P-x) for x in a);packed_b=sum(1<<(T+P-x) for x in b)
        j=(packed_a^packed_b).bit_length()-1
        for t in range(24):
            oldroot={x for x in labels if labels[x]==r};front=max(oldroot)
            assert front==T+P+t-j
            an=physical(a);bn=physical(b)
            newlabels={x:labels[min(y for y in (x-1,x,x+1) if y in labels)] for x in an^bn}
            newroot={x for x in newlabels if newlabels[x]==r}
            assert newroot=={x for x in an^bn if x<=front+1}
            packed_a=phi(packed_a);packed_b=phi(packed_b)
            j+=lowbit((packed_a^packed_b)>>j)
            assert max(newroot)==T+P+t+1-j
            a,b,labels=an,bn,newlabels;checks+=1

cases={(0,2**k) for k in range(13)}
for T in [1,2,7,31,127,511,2047,8191,32767,65535]:
    for P in [1,2,3,4,16,256,1024]:cases.add((T,P))
rng=random.Random(1330302026)
for _ in range(16):cases.add((rng.randrange(65536),rng.randrange(1,1025)))
needed=sorted({v for T,P in cases for v in [T,T+P]});snapshots={};a=1;wanted=set(needed)
for t in range(needed[-1]+1):
    if t in wanted:snapshots[t]=a
    a=phi(a)

records=[];events=Counter()
for T,P in sorted(cases,key=lambda tp:(tp[0]+tp[1],tp)):
    frame=T+P;a=snapshots[T]<<P;b=snapshots[T+P];j=(a^b).bit_length()-1
    j0=j;t=0;front=frame-j;maxretreat=0;maxdebt=0
    horizon=8*frame+1024
    # Full independent mask updates validate the shortcut throughout small cases.
    track_mask=frame<=4096;mask=1<<j
    while front<0 and t<horizon:
        context=tuple(((z>>(j-d))&1) if j>=d else 0 for z in [a,b] for d in range(3))
        an=phi(a);bn=phi(b);d=an^bn
        skipped=lowbit(d>>j);j+=skipped;t+=1
        if track_mask:
            mask=d&(mask|(mask<<1)|(mask<<2))
            assert lowbit(mask)==j
            assert mask==d&~((1<<j)-1)
        events[(context,skipped)]+=1
        maxretreat=max(maxretreat,skipped-1);maxdebt=max(maxdebt,j-j0)
        front=frame+t-j;a,b=an,bn
    assert front<=0
    rec={'T':T,'P':P,'horizon':horizon,'first_hit':t if front==0 else None,
         'last_time':t,'last_front':front,'initial_greedy_index':j0,
         'total_skipped_zeros':j-j0,'largest_one_step_retreat':maxretreat,
         'full_mask_crosscheck':track_mask}
    assert front==-frame+t-rec['total_skipped_zeros']
    records.append(rec)
    print(json.dumps(rec),flush=True)
out={'finite_only':True,'Lean_verified':False,'independent_physical_steps':checks,'rng_seed':1330302026,
     'case_count':len(records),'records':records,
     'context_events':[{'context':list(c),'skipped_zeros':k,'count':n} for (c,k),n in sorted(events.items())],
     'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(root/'greedy-front.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'completed_cases':len(records),'no_hit':[(r['T'],r['P']) for r in records if r['first_hit'] is None],
                  'worst_ratio':max((r['first_hit']/(r['T']+r['P']),r['T'],r['P']) for r in records if r['first_hit'] is not None),
                  'seconds':out['seconds']}),flush=True)
