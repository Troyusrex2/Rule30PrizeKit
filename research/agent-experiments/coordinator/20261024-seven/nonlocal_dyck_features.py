"""Directed Dyck reductions as nonnegative nonlocal row features."""
import itertools,random
import numpy as np

def dyck(w,perm):
    stack=[];peak=0
    for a in w:
        b=perm[a]
        if stack and stack[-1] in (0,2) and b==stack[-1]+1:stack.pop()
        else:stack.append(b);peak=max(peak,len(stack))
    return len(stack),peak,*[stack.count(i) for i in range(4)]

def features(w):
    ans=[1]
    for mask in range(1,15):
        height=lo=hi=0
        for a in w:
            height+=1 if mask>>a&1 else -1;lo=min(lo,height);hi=max(hi,height)
        ans += [-lo,height-lo,height-2*lo,hi,hi-height]
    for perm in itertools.permutations(range(4)):ans.extend(dyck(w,perm))
    assert min(ans)>=0
    return np.array(ans,dtype=np.int64)

def controls():
    rng=random.Random(302528);checks=0
    for perm in itertools.permutations(range(4)):
        for n in range(20):
            w=[rng.randrange(4) for _ in range(n)];red=[perm[a] for a in w]
            while True:
                at=next((i for i in range(len(red)-1) if (red[i],red[i+1]) in [(0,1),(2,3)]),None)
                if at is None:break
                red=red[:at]+red[at+2:]
            got=dyck(w,perm);assert got[0]==len(red) and got[2:]==tuple(red.count(i) for i in range(4));checks+=1
    return {'independent_directed_rewrite_cases':checks,'all_passed':True}
