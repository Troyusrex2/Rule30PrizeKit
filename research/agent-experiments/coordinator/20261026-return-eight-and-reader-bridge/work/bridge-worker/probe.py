"""Bounded product construction, not a width or temporal-clock census."""
import json
from collections import deque
from pathlib import Path

OUT=Path(__file__).parent
reader=[[0,1,2,3],[4,5,6,7],[8,9,10,11],[12,13,14,12],[15,5,15,7],[4,15,6,15],[16,13,15,12],[12,15,14,16],[15,15,10,11],[16,15,14,12],[8,9,15,15],[12,13,15,16],[12,15,15,12],[16,15,14,16],[16,13,15,16],[15,15,15,15],[15,15,15,15]]
safe=[[0,1],[2,3],[4,3],[2,5],[6,6],[7,8],[9,9],[9,10],[10,10],[11,12],[12,11],[11,11],[11,11]]
accept={1,2,3,4,5,12}
def extend(p,r,v):
    out=v
    for t in range(8):
        v^=((p>>t)|(r>>t))&1
        out|=v<<(t+1)
    return out

# Rejecting safety state11 cannot subsequently become accepting. Hence paths
# with both endpoints accepting never visit it, making this graph all-width.
# State records reader, safety A/B, current and older 9-bit histories A/B.
start=(0,0,0,0,0,0,0)
states=[start]; ids={start:0}; paths={start:([],[])}; edges=[]
for q in states:
    rd,qa,qb,pa,ra,pb,rb=q
    row=[]
    for a,b in ((0,0),(0,1),(1,0),(1,1)):
        na,nb=safe[qa][a],safe[qb][b]
        if na==11 or nb==11:
            row.append(None);continue
        n=(reader[rd][2*a+b],na,nb,extend(pa,ra,a),pa,extend(pb,rb,b),pb)
        if n not in ids:
            ids[n]=len(states);states.append(n)
            xa,xb=paths[q];paths[n]=(xa+[a],xb+[b])
        row.append(ids[n])
    edges.append(row)
bad=[]; finals=[]
for i,q in enumerate(states):
    rd,qa,qb,pa,ra,pb,rb=q
    if qa in accept and qb in accept and pa==pb:
        finals.append(i)
        if rd not in {0,3,12,16}:bad.append({'state':q,'path':paths[q]})
report={'kind':'exact finite product, closed over every paired-word length',
        'states':len(states),'live_edges':sum(e is not None for r in edges for e in r),
        'equal_safe_final_states':len(finals),'bad':bad}
(OUT/'product.json').write_text(json.dumps({'report':report,'states':states,'edges':edges},indent=2))
print(json.dumps(report))

# One structurally selected family, not a width census: reader aliases 101
# and 011 reach state12; a shared arbitrary tail preserves its acceptance.
def F(xs):
    return [v ^ ( (xs[i-1] if i>0 else 0) | (xs[i-2] if i>1 else 0)) for i,v in enumerate(xs)]
def orbit(xs):
    rows=[xs];y=F(xs)
    while y!=xs:
        rows.append(y);y=F(y)
        assert len(rows)<1024
    return rows
records=[]
for tail in ([0]*9,):
    a=[1,0,1]+tail;b=[0,1,1]+tail
    qa=0
    for aa,bb in zip(a,b):qa=reader[qa][2*aa+bb]
    oa,ob=orbit(a),orbit(b)
    trace=[x[-1] for x in oa]
    periods=[p for p in range(1,len(trace)+1) if len(trace)%p==0 and all(trace[t]==trace[(t+p)%len(trace)] for t in range(len(trace)))]
    resets=[t for t in range(len(oa)) if not oa[t][-1] and not oa[(t+1)%len(oa)][-1]]
    records.append({'a':a,'b':b,'reader':qa,'orbit_lengths':[len(oa),len(ob)],'least_trace_period':min(periods),
                    'same_trace':all(oa[t%len(oa)][-1]==ob[t%len(ob)][-1] for t in range(max(len(oa),len(ob)))),
                    'safe':all(oa[t][-1] or oa[(t+1)%len(oa)][-1] for t in range(len(oa))),
                    'parent_traces_equal':all(oa[t%len(oa)][-2]==ob[t%len(ob)][-2] for t in range(max(len(oa),len(ob)))),
                    'reset_times':resets,'all_resets_have_three_white_cells':all(oa[t][-3:]==ob[t][-3:]==[0,0,0] for t in resets),
                    'trace':''.join(str(x[-1]) for x in oa)})
(OUT/'alias-controls.json').write_text(json.dumps(records,indent=2))
print(json.dumps(records))
