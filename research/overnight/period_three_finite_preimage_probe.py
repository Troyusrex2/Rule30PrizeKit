"""Exact finite-state discovery for finite three-step preimages.

This constructs an inverse transducer for the 010-boundary left evolution,
with earlier head phases (*,0,1). No graph statement here is Lean verified.
No eventual-period exclusion or prize claim follows from these controls.
"""
from collections import deque
import json
from pathlib import Path
import random


def step(a,b):return (a>>1)^(a|(a<<1)|b)


def G(a):return step(step(step(a,0),1),0)


def delta(state,bit):
    out=0;source=bit
    for j in range(3):
        cur=(state>>(2*j))&1;prev=(state>>(2*j+1))&1
        new=source^(cur|prev);out|=(new|(cur<<1))<<(2*j);source=cur
    return out


def zero_basin():
    accepted={};rejected=[]
    for s in range(64):
        state=s;seen=set();n=0
        while state and state not in seen:
            seen.add(state);state=delta(state,0);n+=1
        if state==0:accepted[s]=n
        else:rejected.append(s)
    assert all((s in accepted)==(delta(s,0) in accepted) for s in range(64))
    return accepted,rejected


BASIN,REJECTED=zero_basin()


def branch(y,head):
    state=9+(head<<4);old=0
    for i in range(y.bit_length()+65):
        old|=((state>>4)&1)<<i
        state=delta(state,(y>>i)&1)
    return old if state==0 else None


def recognizer():
    initial=(9,25);seen={initial};queue=deque([initial]);edges={}
    while queue:
        u=queue.popleft();out=[]
        for bit in (0,1):
            v=tuple(delta(s,bit) for s in u);out.append(v)
            if v not in seen:seen.add(v);queue.append(v)
        edges[u]=out
    # Exact finite refinement, with acceptance invariant under zero padding.
    partition={u:int(any(s in BASIN for s in u)) for u in seen}
    while True:
        codes={};new={}
        for u in sorted(seen):
            key=(partition[u],partition[edges[u][0]],partition[edges[u][1]])
            if key not in codes:codes[key]=len(codes)
            new[u]=codes[key]
        if len(set(new.values()))==len(set(partition.values())):partition=new;break
        partition=new
    states=[None]*(max(partition.values())+1)
    for u in seen:
        record={'accepting':any(s in BASIN for s in u),'next':[partition[v] for v in edges[u]]}
        i=partition[u]
        if states[i] is not None:assert states[i]==record
        states[i]=record
    return {'initial':partition[initial],'states':states,'raw_pair_states':len(seen)}


def accepts(y,machine):
    state=machine['initial']
    for i in range(y.bit_length()):state=machine['states'][state]['next'][(y>>i)&1]
    return machine['states'][state]['accepting']


def main():
    machine=recognizer();forward=accepted=accepted_words=checked=0;ambiguity=good_ambiguity=None
    for a in range(1<<12):
        if a&7 not in (0,7):continue
        y=G(a);pred=[p for p in (branch(y,0),branch(y,1)) if p is not None]
        assert a in pred and accepts(y,machine)
        forward+=1
    for y in range(1<<14):
        pred=[p for p in (branch(y,0),branch(y,1)) if p is not None]
        assert len(pred)<=2 and bool(pred)==accepts(y,machine)
        accepted_words+=int(bool(pred))
        for a in pred:
            assert G(a)==y and a&7 in (0,7)
            accepted+=1
        if len(pred)==2 and ambiguity is None:ambiguity={'word':y,'finite_preimages':pred}
        if len(pred)==2 and y&7 in (0,7) and good_ambiguity is None:
            good_ambiguity={'word':y,'finite_preimages':pred}
        checked+=1
    rng=random.Random(2026102410)
    for _ in range(512):
        a=rng.getrandbits(rng.randrange(3,200));a=(a&~7)|rng.choice((0,7));y=G(a)
        assert branch(y,a&1)==a and accepts(y,machine)
        other=branch(y,1-(a&1))
        if other is not None:assert G(other)==y and other&7 in (0,7)
    report={'finite_experiment_only':True,'Lean_verified':False,'full_problem_claim':False,
            'C3w_011_proved':False,'zero_input_accepting_states':sorted(BASIN),
            'maximum_zero_flush_to_finite_preimage':max(BASIN.values()),
            'inverse_transducer_states':64,'forward_image_examples':forward,
            'all_tested_current_words':checked,'accepted_tested_current_words':accepted_words,
            'accepted_tested_preimage_branches':accepted,
            'wide_random_forward_controls':512,'unique_finite_preimage_claim':False,
            'first_nonunique_finite_preimage_example':ambiguity,
            'first_good_current_nonunique_example':good_ambiguity,
            'all_controls_passed':True,'recognizer':machine}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k!='recognizer'}))
    print(json.dumps({'raw_pair_states':machine['raw_pair_states'],'minimal_DFA_states':len(machine['states'])}))


if __name__=='__main__':main()
