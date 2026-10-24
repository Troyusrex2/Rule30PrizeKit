"""Bounded exact synthesis search for the incoming ordered-product rank."""
import itertools, random, time
from core import canonical, phi, save

I=(1,0,0,1)
def mul(a,b):
    x,y,z,w=a;v,s,t,u=b
    return x*v+y*t,x*s+y*u,z*v+w*t,z*s+w*u

def word(a,b,c):
    n=max(a.bit_length(),b.bit_length(),c+1);ans=[]
    for i in range(n):
        if i==c:ans.append(4)
        ans.append(2*((a>>i)&1)+((b>>i)&1))
    return tuple(ans)

def rank(word,mats):
    h=I
    for k in word:h=mul(h,mats[k])
    return abs(h[1])+abs(h[2])

def constraints():
    result=[];seen=set()
    for T in range(16):
        for P in range(1,9):
            a,b,c=canonical(T,P)
            for step in range(16):
                A,B=a,b;equal=True
                for u in range(3):
                    if ((A^B)>>(c+u))&1:equal=False;break
                    A=phi(A);B=phi(B)
                key=a,b,c
                if equal and key not in seen:
                    seen.add(key)
                    result.append((word(a,b,c),word(phi(phi(a)),phi(phi(b)),c+2),key))
                a=phi(a);b=phi(b);c+=1
    return sorted(result,key=lambda x:len(x[0]))

def main():
    start=time.monotonic();rng=random.Random(307025);con=constraints()
    small=[m for m in itertools.product((-1,0,1),repeat=4) if abs(m[0]*m[3]-m[1]*m[2])==1]
    best=-1;records=[];survivors=[];tested=0
    # Deterministic random coverage, not exhaustive enumeration of 5^20.
    trials=100000
    for trial in range(trials):
        if trial<50000:mats=tuple(rng.choice(small) for _ in range(5))
        else:mats=tuple(tuple(rng.randrange(-2,3) for _ in range(4)) for _ in range(5))
        passed=0
        for before,after,key in con:
            r=rank(before,mats);s=rank(after,mats)
            if s>=r:break
            passed+=1
        tested+=1
        if passed>best:
            best=passed;rec={'trial':trial,'passed_prefix':passed,'matrices':mats}
            if passed<len(con):rec['counterexample']={'a':key[0],'b':key[1],'c':key[2],'rank_before':r,'rank_after':s}
            records.append(rec);print(rec,flush=True)
        if passed==len(con):survivors.append(mats)
    out={'seed':307025,'tested':tested,'constraints':len(con),
         'small_bank_size':len(small),'scope':'50000 sampled invertible {-1,0,1} tuples; 50000 sampled {-2,-1,0,1,2} tuples',
         'best_candidates':records,'survivors':survivors,
         'seconds':round(time.monotonic()-start,3),
         'limitation':'No survivor does not exclude unsampled matrices, larger dimensions, or other rank functions.'}
    save('matrix-rank.json',out);print({'stage':'complete',**{k:out[k] for k in ('tested','constraints','seconds')},'survivors':len(survivors)},flush=True)

if __name__=='__main__':main()
