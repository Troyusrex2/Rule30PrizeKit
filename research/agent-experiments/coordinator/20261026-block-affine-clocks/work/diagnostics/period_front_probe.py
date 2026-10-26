"""Falsify white-boundary period monotonicity or nonconstant-OR rigidity.
Larger censuses are only bounded diagnostics and are never an all-clock proof.
"""
from pathlib import Path
import time,json
r=Path(__file__).resolve().parent;start=time.monotonic();CAP=1000000
def integral(g,b,P):
    mask=(1<<P)-1;x=g;s=1
    while s<P:x^=x<<s;s*=2
    return ((x<<1)&mask)^(mask if b else 0)
def period(x,P):
    while P>1:
        h=P//2;lo=x&((1<<h)-1)
        if x>>h!=lo:break
        P=h;x=lo
    return P
reports=[];drops=[];or_collision=None
for P in [2,4,8,16,32,64]:
    states=[(0,0)];index={(0,0):0};parents=[None];depth=[0];periods=[1];groups={0:0};at=0;edges=0;merges=0;mask=(1<<P)-1
    def word(i):
        out=[]
        while parents[i] is not None:i,b=parents[i];out.append(b)
        return list(reversed(out))
    while at<len(states) and len(states)<CAP and time.monotonic()-start<60:
        u,v=states[at];g=u|v
        if g.bit_count()%2==0:
            for bit in [0,1]:
                w=integral(g,bit,P);edges+=1;s=(v,w)
                if s in index:
                    if max(period(v,P),period(w,P))>2:merges+=1
                    continue
                i=len(states);index[s]=i;states.append(s);parents.append((at,bit));depth.append(depth[at]+1);pw=period(w,P);periods.append(pw)
                if periods[at]>pw:
                    drops.append({'clock':P,'initial_bits':word(i),'old_period':periods[at],
                                  'new_period':pw,'old_profile':hex(v),'new_profile':hex(w)})
                    break
                gn=v|w
                if gn not in groups:groups[gn]=i
                elif gn not in [0,mask] and states[groups[gn]][1]!=w:
                    j=groups[gn]
                    or_collision={'clock':P,'initial_a':word(j),'initial_b':word(i),
                                  'left_pair':[hex(z) for z in states[j]],'right_pair':[hex(z) for z in s],
                                  'shared_OR':hex(gn)}
                    break
        at+=1
        if drops or or_collision:break
    closed=at==len(states)
    rep={'clock':P,'states':len(states),'processed':at,'edges_checked':edges,'closed':closed,
         'period_drop_found':bool(drops),'nonconstant_OR_collision_found':or_collision is not None,
         'maximum_shortest_word_length':max(depth),'merges_outside_period_two_core':merges,
         'seconds_total':round(time.monotonic()-start,3)}
    reports.append(rep);print(json.dumps(rep),flush=True)
    if not closed or drops or or_collision:break
out={'reports':reports,'period_drops':drops,'nonconstant_OR_collision':or_collision,
     'all_clock_monotonicity_proved':False,'all_clock_OR_rigidity_proved':False,
     'Lean_verified':False,'full_problem_solved':False}
(r/'period-front-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'period_drops':drops,'OR_collision':or_collision}),flush=True)
