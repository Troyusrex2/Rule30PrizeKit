"""Finite seed window catalogs and a sound but deliberately weak closure."""
import time
from core import phi,save

def successor(word,w,left,right):
    padded=(word<<1)|right|(left<<(w+1))
    # Here bit0 is physical right, so output = shifted-left XOR center|right.
    return ((padded>>2)^((padded>>1)|padded))&((1<<w)-1)

def closure(w):
    # Crop the physical update of every unknown boundary extension.
    # successor formula independently checked against a per-cell truth table.
    for x in range(1<<w):
        for l in (0,1):
            for r in (0,1):
                bits=[r]+[(x>>i)&1 for i in range(w)]+[l]
                expected=sum((bits[i+1]^(bits[i]|bits[i-1]))<<(i-1) for i in range(1,w+1))
                assert successor(x,w,l,r)==expected
    seen={0};front=[0];rounds=[]
    while front:
        new=set()
        for x in front:
            for l in (0,1):
                for r in (0,1):
                    y=successor(x,w,l,r)
                    if y not in seen:new.add(y)
        seen.update(new);front=list(new);rounds.append(len(seen))
    assert len(seen)==1<<w
    return {'width':w,'closure_size':len(seen),'round_sizes':rounds}

def main():
    started=time.monotonic();widths=(20,21,22,23,24)
    catalogs=[bytearray(1<<w) for w in widths];counts=[0]*len(widths)
    masks=[(1<<w)-1 for w in widths];snapshots=[];a=1
    horizon=1000000
    for t in range(horizon):
        word=(a>>max(0,t-12)) if t>=12 else a<<(12-t)
        for i,w in enumerate(widths):
            v=(word>>(12-w//2))&masks[i]
            if not catalogs[i][v]:catalogs[i][v]=1;counts[i]+=1
        a=phi(a)
        if t+1 in (1000,10000,100000,250000,500000,750000,1000000):
            row={'time_samples':t+1,'distinct':dict(zip(widths,counts)),
                 'seconds':round(time.monotonic()-started,3)}
            snapshots.append(row);print(row,flush=True)
            save('orbit-catalog-progress.json',snapshots)
    out={'snapshots':snapshots,'closure':[closure(w) for w in range(1,11)],
         'limitation':'Finite absence is not future impossibility. Closure under arbitrary exterior bits fills every word, already from zero.',
         'seconds':round(time.monotonic()-started,3)}
    save('orbit-catalog.json',out)

if __name__=='__main__':main()
