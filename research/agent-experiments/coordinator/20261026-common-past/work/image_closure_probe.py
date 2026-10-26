from pathlib import Path
import hashlib,itertools,json
ROOT=Path(__file__).resolve().parent
width=9;steps=96
def step(a):return (a<<2) ^ ((a<<1)|a)
def finite_preimage(x):
    c=r=0;pre=0
    for p in range(x.bit_length()-1,-1,-1):
        l=((x>>p)&1)^(c|r)
        if p>=1:pre|=l<<(p-1)
        r,c=c,l
    return (pre if c==r==0 else None)
for a in range(256):
    assert finite_preimage(step(a))==a<<1, (a,step(a),finite_preimage(step(a)),a<<1)
members={a:finite_preimage(a) for a in range(1<<width)}
rows=[]
for a in range(1<<width):
    r=[a]
    for t in range(steps):r.append(step(r[-1]))
    rows.append(r)
seen={};bad=[];checked=0;collisions=0
for a,b in itertools.combinations(range(1<<width),2):
    h=hashlib.sha256()
    for t in range(steps+1):h.update((rows[a][t]^rows[b][t]).to_bytes((width+2*t+7)//8,'little'))
    key=(h.digest(),a&b)
    pair=(a,b);kind=(members[a] is not None,members[b] is not None)
    checked+=1
    if key in seen:
        collisions+=1
        for old_kind,(c,d) in seen[key].items():
            if (kind==(True,True)) != (old_kind==(True,True)):
                assert all((rows[a][t]^rows[b][t])==(rows[c][t]^rows[d][t]) for t in range(steps+1))
                bad.append({'a':a,'b':b,'c':c,'d':d,'finite_images':[members[q] is not None for q in [a,b,c,d]]})
        seen[key][kind]=pair
    else:seen[key]={kind:pair}
    if len(bad)>=10:break
out={'width':width,'future_steps':steps,'pairs_checked':checked,'pair_collisions':collisions,
     'finite_image_rows':sum(x is not None for x in members.values()),'failure_candidates':bad,
     'finite_only':True,'Lean_verified':False,'all_time_claim_proved':False}
(ROOT/'image-closure-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out),flush=True)
