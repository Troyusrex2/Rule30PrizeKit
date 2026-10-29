from pathlib import Path
import json,time,hashlib,itertools
ROOT=Path(__file__).resolve().parent;start=time.monotonic();WIDTH=24
def rotate(s,r):return s[r:]+s[:r]
def canonical(s):
    n=len(s);ss=s+s;i=0;j=1;k=0
    while i<n and j<n and k<n:
        if ss[i+k]==ss[j+k]:k+=1;continue
        if ss[i+k]>ss[j+k]:
            i+=k+1
            if i<=j:i=j+1
        else:
            j+=k+1
            if j<=i:j=i+1
        k=0
    r=min(i,j);return rotate(s,r),r
controls=0
for n in range(1,9):
    for bits in itertools.product((0,1),repeat=n):
        s=bytes(bits);c,r=canonical(s);assert c==min(rotate(s,j) for j in range(n));controls+=1
assert canonical(bytes((0,0,1,1)))[0]==canonical(bytes((1,1,0,0)))[0]
size=1<<WIDTH;mask=size-1;seen=bytearray(size);classes={};states=0;cycles=0;counter=None;special=0
for seed in range(size):
    if seen[seed]:continue
    orbit=[];here=seed
    while not seen[here]:
        seen[here]=1;states+=1;orbit.append(here);here=(here^((here<<1)|(here<<2)))&mask
    assert here==seed;cycles+=1
    a=bytes((w>>(WIDTH-2))&1 for w in orbit);b=bytes((w>>(WIDTH-1))&1 for w in orbit)
    p=len(b)
    while p>1 and b[:p//2]==b[p//2:p]:p//=2
    if any(a[t]!=a[t%p] for t in range(len(a))):
        counter={'kind':'actual period drop','seed':seed,'older_diagonal':WIDTH-2,'newer_diagonal':WIDTH-1,'cycle':orbit,'newer_period':p};break
    a=a[:p];b=b[:p]
    if p<=2:special+=1;continue
    key,r=canonical(b);value=rotate(a,r)
    if key in classes:
        old=classes[key]
        if old['older']!=value:
            counter={'kind':'same nonalternating newer profile, distinct predecessors','width':WIDTH,'first_seed':old['seed'],'first_rotation':old['rotation'],'second_seed':seed,'second_rotation':r,'common_newer':list(key),'first_older':list(old['older']),'second_older':list(value),'period':p};break
    else:classes[key]={'older':value,'seed':seed,'rotation':r}
    if cycles%512==0:assert time.monotonic()-start<60
out={'scope':'finite numerical census, not Lean proof','width':WIDTH,'complete':states==size and counter is None,'states':states,'cycles':cycles,'nonalternating_profile_classes':len(classes),'special_period_one_two_cycles':special,'counterexample':counter,'canonical_rotation_controls':controls,'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='counterexample'}))
if counter:print(json.dumps({k:v for k,v in counter.items() if k not in ('cycle','common_newer','first_older','second_older')}))
