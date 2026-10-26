"""Search all reachable temporal-column pairs at increasing exact clocks.
This searches for a collision-clock counterexample, not just DFA accuracy.
"""
from pathlib import Path
import json,time
from collections import Counter
ROOT=Path(__file__).resolve().parent
CAP=150000;start=time.monotonic();reports=[];violations=[]
def integral(g,i,P):
    mask=(1<<P)-1;x=g;s=1
    while s<P:x^=x<<s;s*=2
    return ((x<<1)&mask)^(mask if i else 0)
def period(x,P):
    while P>1:
        half=P//2;lo=x&((1<<half)-1)
        if x>>half!=lo:break
        P=half;x=lo
    return P
for P in [2,4,8,16,32,64,128,256,512,1024]:
    states=[(0,0)];index={(0,0):0};parents=[None];at=0;edges=0;closed=True;begin=time.monotonic()
    while at<len(states):
        if len(states)>CAP or time.monotonic()-start>60:closed=False;break
        u,v=states[at];g=u|v
        if g.bit_count()%2==0:
            for bit in [0,1]:
                state=(v,integral(g,bit,P));edges+=1
                if state not in index:index[state]=len(states);states.append(state);parents.append((at,bit))
        at+=1
    groups={}
    for i,(u,v) in enumerate(states):groups.setdefault(u|v,[]).append(i)
    collisions=0;nonconstant_collisions=0
    mask=(1<<P)-1
    for g,group in groups.items():
        if len(group)<2:continue
        for ix,i in enumerate(group):
            for j in group[ix+1:]:
                u,v=states[i];up,vp=states[j]
                if v==vp:continue
                collisions+=1
                if g not in [0,mask]:
                    nonconstant_collisions+=1
                    for init in [0,1]:
                        if g.bit_count()%2:continue
                        q=integral(g,init,P);d=v^vp
                        if ((~q)&d&mask) and (period(q,P)!=2 or period(d,P)>2):
                            def word(k):
                                w=[]
                                while parents[k] is not None:k,b=parents[k];w.append(b)
                                return list(reversed(w))
                            violations.append({'clock':P,'right_a':word(i),'right_b':word(j),'shared_initial':init,
                                               'q_hex':hex(q),'d_hex':hex(d),'q_period':period(q,P),'d_period':period(d,P)})
                            break
                if violations:break
            if violations:break
        if violations:break
    distributions=Counter();unbalanced=[]
    for v in {v for _,v in states}:
        p=period(v,P);small=v&((1<<p)-1);black=small.bit_count()
        distributions[str((p,black))]+=1
        if p>1 and black*2!=p and len(unbalanced)<4:unbalanced.append({'period':p,'black':black,'hex':hex(small)})
    rec={'clock':P,'states':len(states),'processed':at,'edges':edges,'closed':closed,
         'OR_collision_pairs_different_adjacent_column':collisions,
         'nonconstant_OR_collision_pairs':nonconstant_collisions,'violations_found':len(violations),
         'minimal_period_blackcount_distribution':dict(distributions),'unbalanced_profile_examples':unbalanced,
         'seconds':round(time.monotonic()-begin,3)}
    reports.append(rec);print(json.dumps(rec),flush=True)
    if violations or not closed:break
out={'reports':reports,'collision_clock_counterexamples':violations,
     'unbounded_classification_proved':False,'Lean_verified':False,'full_problem_solved':False}
(ROOT/'column-graph.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
