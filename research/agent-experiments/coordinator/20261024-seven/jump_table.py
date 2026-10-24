"""Exact bit-parallel return map above the verified width-34 front cycle.

Experimental instrument; its parallel semantics are not yet formalized here.
"""
import argparse,json,random,time
from core import phi,save,HERE

def scalar(a,steps,k):
    mask=(1<<k)-1
    for _ in range(steps):a=(phi(a)^1)&mask
    return a

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--bits',type=int,default=12);args=parser.parse_args()
    m=args.bits;N=1<<m;ALL=(1<<N)-1;lowK=34;lowmask=(1<<lowK)-1
    lo=13;planes=[sum(((p>>i)&1)<<p for p in range(N)) for i in range(m)]
    start=time.monotonic();prefix=None
    for t in range(65536):
        if t==61005:prefix=(lo,planes.copy())
        prev1=ALL if lo>>(lowK-1)&1 else 0;prev2=ALL if lo>>(lowK-2)&1 else 0
        new=[]
        for x in planes:
            new.append(x^(prev1|prev2));prev2,prev1=prev1,x
        lo=(phi(lo)^1)&lowmask;planes=new
    assert lo==13
    table=[sum(((planes[i]>>u)&1)<<i for i in range(m)) for u in range(N)]
    pretable=[prefix[0]|sum(((prefix[1][i]>>u)&1)<<(lowK+i) for i in range(m)) for u in range(N)]
    rng=random.Random(307030);checks=0
    for u in [0,N-1]+[rng.randrange(N) for _ in range(30)]:
        a=13|(u<<lowK)
        assert scalar(a,65536,lowK+m)==13|(table[u]<<lowK)
        assert scalar(a,61005,lowK+m)==pretable[u];checks+=2
    assert len(set(table))==N
    polys=[]
    for i in range(m):
        anf=[((table[u]^u)>>i)&1 for u in range(N)]
        for bit in range(m):
            for u in range(N):
                if u>>bit&1:anf[u]^=anf[u^(1<<bit)]
        terms=[u for u,x in enumerate(anf) if x]
        polys.append({'bit':i,'delta_degree':max((x.bit_count() for x in terms),default=-1),
                      'delta_term_count':len(terms),'delta_terms_masks':terms if len(terms)<=64 else None})
    orbit=[];u=0
    while not orbit or u:
        orbit.append(u);u=table[u]
        assert len(orbit)<=N
    bad=[]
    for j,u in enumerate(orbit):
        row=pretable[u];r=61005+65536*j;found=None
        for s in range(lowK+m):
            if (r+s)%2==0 and row&1==0:found=s;break
            row=(row>>1)^(row|(row<<1))
        if found is None:bad.append(j)
    report={'upper_bits':m,'low_width':lowK,'base_period':65536,'lanes':N,
            'scalar_controls':checks,'jump_table_is_permutation':True,
            'return_map_zero_orbit':orbit,'unresolved_rare_lifts_in_zero_orbit':bad,
            'delta_ANF':polys,'seconds':round(time.monotonic()-start,3),
            'Lean_verified':False,'full_problem_solved':False}
    save(f'jump-table-{m}.json',report)
    (HERE/f'jump-table-{m}-data.json').write_text(json.dumps({'return':table,'prefix':pretable})+'\n',encoding='utf-8')
    print({'seconds':report['seconds'],'orbit_length':len(orbit),'bad_lifts':bad,
           'ANF':[(x['bit'],x['delta_degree'],x['delta_term_count']) for x in polys]},flush=True)

if __name__=='__main__':main()
