"""Test a local ranking candidate on the three prior, known finite histories.
At each legal complete return ask whether width - 2*max_white_past
strictly decreases. One non-decreasing step refutes the proposed ranking.
"""
def step(x):
    return (x >> 1) ^ (x | (x << 1))

def zero_parent(y):
    assert y
    a=b=x=0
    for j in range(y.bit_length()):
        a,b=b,((y>>j)&1)^(a|b)
        x|=b<<(j+1)
    if a|b:
        return None
    assert step(x)==y and x%2==0
    return x

def valuation(y):
    n=0
    while (w:=zero_parent(y)) is not None:
        n+=1
        y=w
    return n

if __name__=='__main__':
    for seed in [2440786724530854946624415088918,348215574720768951329435505750294,2483979780129110]:
        x=seed; previous=None; transitions=[]
        for t in range(150):
            if not x&1:
                if previous and t-previous[0] not in (6,10):break
                n=valuation(x)
                rec=(t,x.bit_length(),n,x.bit_length()-2*n)
                if previous:transitions.append((previous,rec))
                previous=rec
            x=step(x)
        print(seed,'nondecreases',sum(b[-1]>=a[-1] for a,b in transitions),'/',len(transitions))
        print('latest',transitions[-3:])
