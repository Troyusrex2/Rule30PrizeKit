"""Construct finite full rows with a genuine 27-tick 011 window around the tested step."""
from functools import lru_cache
from descent import tick,macro


@lru_cache(None)
def start(slot):
    right=0
    for t in range(900+3*slot):
        c=int(t%3!=0)
        right=(right<<1|c)^(right|right>>1)
    init=right
    cs=[int(t%3!=0) for t in range(28)]
    rs=[]
    for c in cs:
        rs.append(right&1)
        right=(right<<1|c)^(right|right>>1)
    x=0
    for j in range(27):
        cs,rs=[z^(a|b) for z,a,b in zip(cs[1:],cs,rs)],cs
        x|=cs[0]<<j
    return x,init


def tested(slot, tail):
    x,right=start(slot)
    x |= tail<<27
    result=None
    for t in range(27):
        c=int(t%3!=0)
        assert ((x&1)^(c|(right&1)))==int((t+1)%3!=0)
        if t==12:
            result=x
        x=tick(x,c)
        if t==14:
            assert x==macro(result)
        right=(right<<1|c)^(right|right>>1)
    return result
