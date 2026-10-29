"""Complete reachable spatial graph at a fixed temporal clock, all widths.

Every edge appends a cyclic temporal column with delta(new)=a OR b.
Initial state is the two white boundary columns. Period bound is explicit.
"""
from collections import deque, Counter
from pathlib import Path
import json, time
from probe import period, delta
ROOT=Path(__file__).resolve().parent
def graph(q,cap=400000,seconds=40):
    start=time.monotonic();mask=(1<<q)-1
    initial=(0,0);queue=deque([initial]);seen={initial:(None,None)}
    edges=0;bad=[];terminal=0;complete=True
    periods={}
    def p(x):
        if x not in periods:periods[x]=period(x,q)
        return periods[x]
    while queue:
        if len(seen)>cap or time.monotonic()-start>seconds:
            complete=False;break
        a,b=queue.popleft();driver=a|b
        if driver.bit_count()%2:
            terminal+=1;continue
        c=0;bit=0
        for t in range(q):
            c|=bit<<t;bit^=(driver>>t)&1
        assert bit==0 and delta(c,q)==driver
        for c in (c,c^mask):
            edges+=1
            if p(c)<p(b):bad.append({'pair':[a,b],'new':c,'periods':[p(a),p(b),p(c)]})
            state=(b,c)
            if state not in seen:
                seen[state]=((a,b),c);queue.append(state)
    rows=sorted([[a,b] for a,b in seen])
    result={'q':q,'complete':complete,'states':len(seen),'edges':edges,'terminal_states':terminal,'frontier':len(queue),'period_drops':len(bad),'witnesses':bad[:3],'seconds':time.monotonic()-start,'state_cap':cap,'seconds_cap':seconds,'kernel_verified':False,'scope':'All spatial widths at temporal period dividing q, only if complete=true'}
    (ROOT/f'CLOCK-{q}-STATES.json').write_text(json.dumps(rows,separators=(',',':'))+'\n')
    return result
if __name__=='__main__':
    result=[graph(q) for q in [2,4,8,16]]
    (ROOT/'CLOCK-GRAPHS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
