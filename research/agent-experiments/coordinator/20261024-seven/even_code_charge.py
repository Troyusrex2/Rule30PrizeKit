"""Test a proposed charge bound on all no-00 free prefixes of bounded length.

Could isolated free zeros require at least as many black even initial cells?
The question is falsified before any claim of an unbounded charge invariant.
"""
from functools import lru_cache
import argparse,random,time
from core import save
from coupled_even_code_probe import even_code,decode,forbidden

def words(n,golden=False):
    out=[(0,0),(1,1)]
    for i in range(1,n):
        new=[]
        for w,run in out:
            if w>>(i-1)&1:new.append((w,0))
            if not golden or run<4:new.append((w|(1<<i),run+1))
        out=new
    return [w for w,_ in out if not golden or w!=((1<<n)-1) or n<5]

def planes_for(ws,n):
    bs=[bytearray((len(ws)+7)//8) for _ in range(n)]
    for j,w in enumerate(ws):
        v=w
        while v:
            bit=(v&-v).bit_length()-1;bs[bit][j>>3]|=1<<(j&7);v&=v-1
    return [int.from_bytes(b,'little') for b in bs]

def even_planes(free,ALL):
    @lru_cache(None)
    def pair(m,k):
        if m==0:return ALL,0
        if m==1:return ALL,(free[k] if k<len(free) else 0)
        e,o=pair(m-1,k);ep,op=pair(m-2,k);en,_=pair(m-1,k+1)
        return o^(e|ep),en^(o|op)
    out=[pair(2*d+2,0)[0] for d in range(len(free))];pair.cache_clear();return out

def sum_planes(planes):
    bits=[]
    for p in planes:
        i=0;carry=p
        while carry:
            if i==len(bits):bits.append(carry);break
            bits[i],carry=bits[i]^carry,bits[i]&carry;i+=1
    return bits

def ge(a,b,ALL):
    same=ALL;greater=0
    for i in reversed(range(max(len(a),len(b)))):
        x=a[i] if i<len(a) else 0;y=b[i] if i<len(b) else 0
        greater|=same&x&(ALL^y);same&=ALL^(x^y)
    return greater|same

def count_masks(planes,n,ALL):
    masks=[]
    for value in range(n+1):
        if value>>len(planes):masks.append(0);continue
        mask=ALL
        for i,p in enumerate(planes):mask&=p if value>>i&1 else ALL^p
        masks.append(mask)
    covered=0
    for mask in masks:
        assert not covered&mask
        covered|=mask
    assert covered==ALL
    return masks

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--max-width',type=int,default=24)
    parser.add_argument('--factor',type=int,default=1);parser.add_argument('--golden',action='store_true')
    parser.add_argument('--profile',action='store_true')
    args=parser.parse_args();assert 1<=args.factor<=8
    filename=f'even-code-charge-factor{args.factor}-golden{int(args.golden)}'+('-profile' if args.profile else '')+'.json'
    out={'records':[],'Lean_verified':False,'full_problem_solved':False,
         'factor':args.factor,'no11111_constraint':args.golden,
         'tested_claim':'factor * black even-code cells >= free zeros'}
    for n in range(1,9):
        expected=[w for w in range(1<<n) if forbidden([(w>>i)&1 for i in range(n)]) is None]
        assert sorted(words(n,True))==expected
    rng=random.Random(302432)
    for n in range(1,args.max_width+1):
        start=time.monotonic();ws=words(n,args.golden);N=len(ws);ALL=(1<<N)-1
        ps=planes_for(ws,n);es=even_planes(ps,ALL);a=sum_planes(es*args.factor);b=sum_planes([ALL^p for p in ps])
        bad=ALL^ge(a,b,ALL)
        for j in set([0,N-1]+[rng.randrange(N) for _ in range(8)]):
            free=[(ws[j]>>i)&1 for i in range(n)]
            u=sum(((p>>j)&1)<<i for i,p in enumerate(es))
            assert u==even_code(free) and decode(u,n)==free
            ca=sum(((p>>j)&1)<<i for i,p in enumerate(a));cb=sum(((p>>j)&1)<<i for i,p in enumerate(b))
            assert ca==args.factor*u.bit_count() and cb==n-ws[j].bit_count()
        row={'free_prefix_length':n,'complete_no00_domain':N,'violations':bad.bit_count(),
             'charge_bound_holds_on_domain':not bad,'seconds':round(time.monotonic()-start,3)}
        if args.profile:
            am=count_masks(a,n*args.factor,ALL);bm=count_masks(b,n,ALL)
            row['max_free_zeros_by_even_black_count']={str(i//args.factor):max(
                j for j,m in enumerate(bm) if m&mask) for i,mask in enumerate(am) if mask}
            row['minimum_even_black_count']=min(i//args.factor for i,m in enumerate(am) if m)
            assert all(v<=(n+1)//2 for v in row['max_free_zeros_by_even_black_count'].values())
            for k,z in row['max_free_zeros_by_even_black_count'].items():
                mask=am[int(k)*args.factor]&bm[z];j=(mask&-mask).bit_length()-1
                u=sum(((p>>j)&1)<<i for i,p in enumerate(es))
                assert u.bit_count()==int(k) and n-ws[j].bit_count()==z
        if bad:
            j=(bad&-bad).bit_length()-1;free=[(ws[j]>>i)&1 for i in range(n)]
            u=even_code(free);assert decode(u,n)==free and args.factor*u.bit_count()<free.count(0)
            row['counterexample']={'free':free,'even_code':u,'even_black_count':u.bit_count(),
                    'free_zero_count':free.count(0),'golden_violation':forbidden(free)}
        out['records'].append(row);save(filename,out);print(row,flush=True)
        if bad and not args.profile:break

if __name__=='__main__':main()
