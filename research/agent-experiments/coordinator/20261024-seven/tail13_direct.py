"""Independent full-row checks of actual exceptional stripe-prefix lengths."""
import time
from core import save

def step(a):return (a>>1)^(a|(a<<1))

def initial(m):
    return (((1<<(m+1))-1)//3)|(13<<m)

def controls():
    cells=0
    for m in (1,3,5,7):
        a=initial(m);row={i+1:(a>>i)&1 for i in range(a.bit_length())}
        for t in range(80):
            for i in range(1,max(row)+1):assert ((a>>(i-1))&1)==row.get(i,0);cells+=1
            old={0:0,**row}
            row={i:(30>>((old.get(i+1,0)<<2)|(old.get(i,0)<<1)|old.get(i-1,0)))&1
                 for i in range(1,max(row)+2)}
            a=step(a)
    return cells

def main():
    out={'independent_physical_cells':controls(),'records':[],'unbounded_claim_from_this_script':False}
    for m in (1,3,61005,126541,388685):
        start=time.monotonic();a=initial(m);death=None
        for t in range(m+46):
            if t%2==0 and a&1==0:death=t;break
            a=step(a)
        assert death is not None and death<=m+45
        row={'stripe_prefix_length':m,'first_even_white_time':death,
             'postarrival_delay':death-m,'seconds':round(time.monotonic()-start,3)}
        out['records'].append(row);save('tail13-direct.json',out);print(row,flush=True)

if __name__=='__main__':main()
