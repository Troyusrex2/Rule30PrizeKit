from pathlib import Path
import hashlib,json,time,random
root=Path(__file__).resolve().parent;start=time.monotonic()
def phi(a):return a^((a<<1)|(a<<2))
def b(a,d):return (a>>d&1) & (1^(a>>(d-1)&1)) if d else a&1
def submasks(r):
    u=r
    while True:
        yield u
        if not u:break
        u=(u-1)&r
def orbit(a,R):
    rows=[a]
    for _ in range(R):rows.append(phi(rows[-1]))
    return rows
def direct_G(rows,r):
    if not r:return 0
    v=0
    for u in submasks(r):v ^= rows[u]>>(2*r-1)&1
    return v
def profile(a,R):
    rows=orbit(a,R)
    m=max(0,a.bit_length()-1)
    cs=[]
    for r in range(R):
        v=0
        for u in range(min(r,m//2)+1):
            if u&r==u:v ^= b(rows[r-u],2*r)
        cs.append(v)
    gs=[0]
    for c in cs:gs.append(gs[-1]^c)
    return rows,cs,gs
rng=random.Random(301635)
controls=0
for a in list(range(64))+[rng.randrange(1<<32) for _ in range(48)]:
    rows,cs,gs=profile(a,96)
    for r in range(96):
        d=0
        for u in submasks(r):d ^= b(rows[u],2*r)
        assert d==cs[r]
        assert gs[r]==direct_G(rows,r)
        assert cs[r]==direct_G(rows,r)^direct_G(rows,r+1)
        controls+=1
records=[]
for a in range(1,256):
    rows,cs,gs=profile(a,512)
    if not(a&1) or ((a>>1)^(a>>2))&1:continue
    bound=2*a.bit_length()+2
    bad=next((r for r in range(bound,513) if gs[r]!=1),None)
    tail=gs[257:513]
    per=next((p for p in range(1,129) if all(tail[i]==tail[i-p] for i in range(p,len(tail)))),None)
    records.append({'row':a,'width':a.bit_length(),'linear_bound':bound,
                    'first_nonone_after_bound':bad,'finite_tail_period':per,
                    'nonones_last256':sum(1-x for x in tail)})
canonical=[];a=1
for t in range(65):
    rows,cs,gs=profile(a,2048)
    nonones=[r for r in range(1,len(gs)) if gs[r]!=1]
    bound=2*a.bit_length()+2
    bad=next((r for r in nonones if r>=bound),None)
    canonical.append({'seed_time':t,'row_width':a.bit_length(),'linear_bound':bound,
                       'first_nonone_after_bound':bad,'last_nonone_through2048':max(nonones,default=None),
                       'nonones':len(nonones),'tail256_nonones':sum(1-x for x in gs[-256:])})
    a=phi(a)
out={'finite_only':True,'full_problem_solved':False,'controls':controls,
     'identity':'C_r=G_(r+1)+G_r; channel telescoping is an exact encoding, not independent control of the full parity.',
     'tested_shortcut':'For seed-low rows G_r=1 whenever r>=2*width+2.',
     'seedlow_rows':records,'canonical_rows':canonical,
     'generic_shortcut_counterexample':next((x for x in records if x['first_nonone_after_bound'] is not None),None),
     'canonical_shortcut_counterexample':next((x for x in canonical if x['first_nonone_after_bound'] is not None),None),
     'elapsed_seconds':time.monotonic()-start}
(root/'echo-operator.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['controls','generic_shortcut_counterexample','canonical_shortcut_counterexample','elapsed_seconds']},indent=2))
