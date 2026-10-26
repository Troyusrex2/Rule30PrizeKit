"""Actual driven finite right halves. Finite observation is not a proof."""
from pathlib import Path
import json, time

root=Path(__file__).resolve().parent

def least_period(s):
    pi=[0]*len(s)
    for i in range(1,len(s)):
        j=pi[i-1]
        while j and s[i]!=s[j]:j=pi[j-1]
        if s[i]==s[j]:j+=1
        pi[i]=j
    return len(s)-pi[-1]

start=time.monotonic();results=[]
steps=65536
for word in ['110','1011','1100','10','1','0']:
    driver=list(map(int,word))
    for initial in [0,1,3,33]:
        state=initial;out=[]
        for t in range(steps):
            c=driver[t%len(driver)]
            out.append(c | (state&1))
            nxt=((state<<1)|c) ^ (state | (state>>1))
            if t<64:
                # Literal physical update over the full active support plus one.
                width=max(1,state.bit_length()+1)
                literal=0
                for j in range(width):
                    left=c if j==0 else (state>>(j-1))&1
                    middle=(state>>j)&1;right=(state>>(j+1))&1
                    literal|=(left ^ (middle|right))<<j
                assert literal==nxt
            state=nxt
        tail=out[-16384:];p=least_period(tail)
        result={'driver':word,'initial_word_integer':initial,'steps':steps,
                'tail_window':len(tail),'tail_least_period':p,
                'small_period_candidate':p if p<=256 else None,
                'tail_distinct_8_blocks':len({tuple(tail[j:j+8]) for j in range(len(tail)-7)}),
                'scope':'finite trace only; no eventual-periodicity or nonperiodicity claim'}
        results.append(result)
        print(json.dumps(result),flush=True)
(root/'finite-right-probe.json').write_text(json.dumps({'results':results,
    'elapsed_seconds':time.monotonic()-start,'literal_full_row_controls':64*len(results)},indent=2)+'\n',encoding='utf-8')
