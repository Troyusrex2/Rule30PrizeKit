from pathlib import Path
import json,math,time
root=Path(__file__).resolve().parent;start=time.monotonic()
rows=[1]
for _ in range(8191):rows.append(rows[-1]^((rows[-1]<<1)|(rows[-1]<<2)))
def source(d,s):return (rows[s]>>d&1)&(1^(rows[s]>>(d-1)&1)) if d else 1
def rho(H):
    delta=rows[H]^1
    return (delta&-delta).bit_length()-1
checks={'physical_cells':0,'prefix_periods':0,'cut_flips':0,'cut_window_sources':0,
        'allones_choose':0,'selected_events_below_cut':0,'direct_leading_binomial_terms':0}
physical={0:1}
for t in range(65):
    for d in range(2*t+4):
        assert rows[t]>>d&1==physical.get(t-d,0);checks['physical_cells']+=1
    physical={p:int(bool(physical.get(p-1,0)) != bool(physical.get(p,0) or physical.get(p+1,0)))
              for p in range(-t-1,t+2)}
for H in range(1,257):
    cut=rho(H)
    assert 0<cut<=2*H-1
    assert source(cut,H-1)==0
    for t in range(129):
        assert rows[H+t]&((1<<cut)-1)==rows[t]&((1<<cut)-1)
        checks['prefix_periods']+=1
        assert (rows[H+t]>>cut&1)==1^(rows[t]>>cut&1)
        checks['cut_flips']+=1
    for v in range(cut//2):
        if 2*v+1<cut:
            assert source(cut,H+v)==1;checks['cut_window_sources']+=1
for e in range(11):
    H=1<<e
    for k in range(H):
        assert math.comb(H-1,k)%2==1;checks['allones_choose']+=1
records=[]
for e in range(13):
    H=1<<e;n=2*H-1;cut=rho(H)
    assert e<cut
    if e<=9:
        for d in range(cut):
            if d%2:continue
            K=H-1-d//2
            for s in range(n):
                selected=((K&(n-1-s))==K) and source(d,s)
                assert bool(selected)==bool(d==0 and s==H-1)
                checks['selected_events_below_cut']+=1
    leading=None;direct=None
    if cut%2==0:
        r=cut//2;K=H-1-r
        u=r;leading=0
        while True:
            leading ^= source(2*r,H-1+r-u)
            if not u:break
            u=(u-1)&r
        assert leading==1
        if e<=8:
            direct=0
            for s in range(n):
                h=n-1-s
                direct ^= (math.comb(h,K)%2 if K<=h else 0)&source(2*r,s)
                checks['direct_leading_binomial_terms']+=1
            assert direct==1
    c=rows[n]>>n&1
    records.append({'e':e,'H':H,'time':n,'rho':cut,'even_leading_parity':leading,
                    'direct_binomial_leading':direct,'center':c,
                    'tail_after_even_leading':c if leading is not None else None})
out={'finite_only':True,'full_problem_solved':False,'all_passed':True,'checks':checks,
     'records':records,'elapsed_seconds':time.monotonic()-start}
(root/'return-controls.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'checks':checks,'elapsed_seconds':out['elapsed_seconds'],'all_passed':True},indent=2))
