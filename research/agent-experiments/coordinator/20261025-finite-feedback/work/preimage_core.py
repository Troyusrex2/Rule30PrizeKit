"""Branch over actual preimages; retain complete finite words, never ghost drivers."""
from pathlib import Path
from fractions import Fraction
import itertools,json,random,time
import feedback_core as core
root=Path(__file__).resolve().parent
start=time.monotonic();rng=random.Random(301725)

def all_preimages(y,boundary,cap=256):
    M=len(y);dp=[[1]*4 for _ in range(M+1)]
    for i in range(M-1,-1,-1):
        for a,b in itertools.product(range(2),repeat=2):
            dp[i][2*a+b]=sum(dp[i+1][2*b+c] for c in range(2) if a^(b|c)==y[i])
    total=sum(dp[0][2*boundary+b] for b in range(2))
    ranks=range(total) if total<=cap else sorted(rng.sample(range(total),cap))
    out=[]
    for rank in ranks:
        a=boundary;b=0
        if rank>=dp[0][2*a]:rank-=dp[0][2*a];b=1
        word=[b]
        for i in range(M):
            for c in range(2):
                if a^(b|c)!=y[i]:continue
                count=dp[i+1][2*b+c]
                if rank<count:break
                rank-=count
            word.append(c);a,b=b,c
        out.append(tuple(word))
    assert len(set(out))==len(out)
    return total,out

