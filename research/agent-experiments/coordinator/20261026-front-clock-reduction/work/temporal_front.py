"""Exact all-time temporal columns, using the proved 2^j period bound.
Finite prefix classification is not an unbounded front-stability theorem.
"""
from pathlib import Path
import argparse,itertools,json
from collections import Counter
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--max-depth',type=int,default=10);args=parser.parse_args()
def repeat(x,old,new):
    while old<new:x|=x<<old;old*=2
    return x
def integral(g,initial,P):
    mask=(1<<P)-1;x=g
    shift=1
    while shift<P:x^=x<<shift;shift*=2
    return ((x<<1)&mask)^(mask if initial else 0)
def minimum_period(bits,P):
    while P>1:
        half=P//2;low=bits&((1<<half)-1)
        if bits>>half!=low:break
        bits=low;P=half
    return P
def columns(initial,n):
    cols=[]
    for j in range(n):
        P=1<<j
        a=repeat(cols[-1],P//2,P) if j else 0
        b=repeat(cols[-2],P//4,P) if j>=2 else 0
        cols.append(integral(a|b,(initial>>j)&1,P))
    return cols
def extend(node):
    j=node['depth'];P=1<<j;mask=(1<<P)-1
    a1,b1,h1=[repeat(node[k][-1],P//2,P) for k in ['a','b','h']]
    a2,b2,h2=[repeat(node[k][-2],P//4,P) for k in ['a','b','h']]
    result=[]
    for ai,bi,hi in [(0,0,0),(1,1,0),(0,1,0),(0,1,1),(1,0,0),(1,0,1)]:
        a=integral(a1|a2,ai,P);b=integral(b1|b2,bi,P)
        h=integral((((~b2)&h1)^((~a1)&h2))&mask,hi,P)
        if ((a^b)&h1)!=(h&(a1^b1)):continue
        result.append({'depth':j+1,'a':node['a']+[a],'b':node['b']+[b],'h':node['h']+[h],
                       'initial':node['initial']+[(ai,bi,hi)]})
    return result

# Independently compare every computed time column to literal prefix iteration.
controls=0
for n in range(1,7):
    mask=(1<<n)-1
    for initial in range(1<<n):
        cols=columns(initial,n);row=initial
        for t in range(1<<(n-1)):
            assert all(((row>>j)&1)==((cols[j]>>(t%(1<<j)))&1) for j in range(n))
            row=(row^((row<<1)|(row<<2)))&mask;controls+=1
records=[];first_live=None
for n in range(3,args.max_depth+1):
    allcols={a:columns(a,n) for a in range(1<<n)}
    groups={}
    for a,c in allcols.items():groups.setdefault(c[-2],[]).append(a)
    candidates=0;alive_counts=[0,0,0];max_extra=0;live_example=None;clocks=Counter();clock_examples={}
    nonalternating_neighbor_disagreements=0;neighbor_example=None;right_clocks=Counter();uncovered_clock_cases=[]
    for group in groups.values():
        for a,b in itertools.combinations(group,2):
            if ((a^b)>>(n-1))&1==0:continue
            ac,bc=allcols[a],allcols[b];mask=(1<<(1<<(n-1)))-1
            if minimum_period(ac[-2],1<<(n-2))!=2 and ac[-3]!=bc[-3]:
                nonalternating_neighbor_disagreements+=1
                if neighbor_example is None:neighbor_example={'a':a,'b':b,'prefix_bits':n}
            if ac[-1]^bc[-1]==mask:continue
            candidates+=1
            cp=(minimum_period(ac[-1]^bc[-1],1<<(n-1)),minimum_period(ac[-2],1<<(n-2)))
            clocks[str(cp)]+=1
            rp=minimum_period(ac[-3]^bc[-3],1<<(n-3));right_clocks[str(rp)]+=1
            if cp[1]!=2 or rp>2:uncovered_clock_cases.append({'a':a,'b':b,'prefix_bits':n,'right_period':rp,'clocks':cp})
            clock_examples.setdefault(str(cp),{'a':a,'b':b,'initial_bits':n})
            node={'depth':n,'a':ac,'b':bc,'h':[0]*(n-1)+[mask],
                  'initial':[((a>>j)&1,(b>>j)&1,int(j==n-1)) for j in range(n)]}
            nodes=[node]
            for extra in range(3):
                nodes=[q for old in nodes for q in extend(old)]
                alive_counts[extra]+=len(nodes)
                if not nodes:break
                max_extra=max(max_extra,extra+1)
                assert len(nodes)<=4096
            if nodes and live_example is None:
                live_example={'a':a,'b':b,'source_depth':n-1,
                              'extensions':len(nodes),'initial':nodes[0]['initial']}
    rec={'prefix_bits':n,'varying_front_candidates':candidates,'extensions_after_1_2_3_columns':alive_counts,
         'maximum_surviving_extra_depth':max_extra,'surviving_example':live_example,
         'front_and_shared_clock_periods':dict(clocks),'clock_examples':clock_examples,
         'nonalternating_neighbor_disagreements':nonalternating_neighbor_disagreements,
         'neighbor_example':neighbor_example,'right_difference_periods':dict(right_clocks),
         'uncovered_clock_cases':uncovered_clock_cases}
    records.append(rec);print(json.dumps(rec),flush=True)
    if live_example and first_live is None:first_live=live_example
out={'controls':controls,'records':records,'first_surviving_front':first_live,
     'finite_prefix_only':True,'all_time_per_tested_prefix':True,'Lean_verified':False,
     'unbounded_front_stability_proved':False}
(ROOT/f'temporal-front-{args.max_depth}.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
