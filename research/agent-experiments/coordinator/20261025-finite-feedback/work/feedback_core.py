from pathlib import Path
from fractions import Fraction
import hashlib,json,random,re,time
root=Path(__file__).resolve().parent;start=time.monotonic()
ref=Path(r'D:\MWB\Rule30\current-reference-3eca-20261024')
text=(ref/'lean/Ruliology/CellularAutomata/Rule30Ether.lean').read_text(encoding='utf-8')
block=text.split('def wallStates :',1)[1].split('\n]',1)[0]
walls=[(int(p),[int(x.strip()=='true') for x in w.split(',')])
       for p,w in re.findall(r'\((\d+), \[([^\]]+)\]\)',block)]
assert len(walls)==109 and all(len(w)==13 for _,w in walls)
tableblock=text.split('def etherTable :',1)[1].split(']]',1)[0]+']]'
table=[[int(x.strip()=='true') for x in w.split(',')]
       for w in re.findall(r'\[([^\[\]]+)\]',tableblock)]
assert len(table)==7 and all(len(w)==4 for w in table)
wallsets=[{sum(x<<i for i,x in enumerate(w)) for p,w in walls if p==q} for q in range(4)]
patterns=[sum(table[(3+p)%7][q]<<i for i,p in enumerate(range(1,142))) for q in range(4)]
def step(row,t):
    row=((row<<1)^(row|(row>>1)))&~1
    return row|int((t+1)%2==0)
def free_stream(code,n):
    row=code|1;out=[]
    for t in range(2*n-1):
        row=step(row,t)
        if t%2==0:out.append(1^(row>>1&1))
    return out
def scalar_free(code,n):
    row={0}|{p for p in range(1,code.bit_length()) if code>>p&1};out=[]
    for t in range(2*n-1):
        row={p for p in range(1,max(row|{1})+2)
             if int(p-1 in row)^(int(p in row)|int(p+1 in row))}
        if (t+1)%2==0:row.add(0)
        else:out.append(int(1 not in row))
    return out
def normalize(prefix,first):
    prefix=list(prefix)
    while prefix and prefix[-1]==1-first:
        prefix.pop();first^=1
    return prefix,first
def trapped(code,cap=384):
    row=code|1;free=[]
    for T in range(cap+1):
        for phaseoffset in [1,3]:
            phase=(T+phaseoffset)%4
            delta=(row>>1)^patterns[phase]
            matched=(delta&-delta).bit_length()-1 if delta else 141
            k=min(128,matched)
            k -= (k-6)%7
            for k in range(k,5,-7):
                w=(row>>(k+1))&8191
                if w in wallsets[phase]:
                    m=len(free)
                    first=1-table[4][(2*m+1+phaseoffset)%4]
                    prefix,first=normalize(free,first)
                    return {'time':T,'ether_width':k,'phase_offset':phaseoffset,
                            'wall_phase':phase,'wall_code':w,'free_prefix':prefix,'tail_first':first}
        if T==cap:break
        row=step(row,T)
        if T%2==0:free.append(1^(row>>1&1))
    return None
def spatial_cycle(prefix,first,cap=20000):
    m=len(prefix);mu=2*m;width=mu+4;mask=(1<<width)-1
    def f(s):return prefix[s] if s<m else first^((s-m)%2)
    cur=sum((1 if t%2==0 else f(t//2))<<t for t in range(width))
    prev=0;seen={};outputs=[]
    for j in range(cap):
        key=(prev,cur)
        if key in seen:
            begin=seen[key];word=outputs[begin:];black=sum(word);period=len(word)
            return {'entry_depth':begin+1,'period':period,'black':black,
                    'density':str(Fraction(black,period)),
                    'charge_ratio':str(Fraction(3*period,4*black)) if black else 'infinite',
                    'C3_positive_drift':period>4*black,
                    'cycle_bits':''.join(map(str,word)),'entry_previous_hex':hex(prev),
                    'entry_current_hex':hex(cur),'temporal_prefix':mu,'temporal_period':4,'states':len(outputs)}
        seen[key]=j;outputs.append(cur&1)
        shifted=(cur>>1)|(((cur>>mu)&1)<<(width-1))
        prev,cur=cur,(shifted^(cur|prev))&mask
    return {'unknown_at_states':len(outputs)}
