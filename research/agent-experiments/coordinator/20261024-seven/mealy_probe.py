"""Exact finite Mealy-model controls and state growth under self-composition.

The three-state model is derived directly here; no group-theoretic result is
assumed. This experiment does not prove temporal nonperiodicity.
"""
from collections import deque
import random,time
from core import phi,save

LIMIT=100000
BASE=[(0,(0,2)),(1,(0,2)),(1,(1,2))]  # A=(A,C), B=(A,C)swap, C=(B,C)swap

def reroot(machine,root):
    order={root:0};queue=deque([root]);out=[]
    while queue:
        s=queue.popleft();flip,trans=machine[s];dest=[]
        for t in trans:
            if t not in order:order[t]=len(order);queue.append(t)
            dest.append(order[t])
        out.append((flip,tuple(dest)))
    return out

def run(machine,a,n):
    state=0;out=0
    for i in range(n):
        x=(a>>i)&1;flip,trans=machine[state]
        out|=(x^flip)<<i;state=trans[x]
    return out

def compose(outer,inner):
    order={(0,0):0};queue=deque([(0,0)]);out=[]
    while queue:
        a,b=queue.popleft();fa,ta=outer[a];fb,tb=inner[b];dest=[]
        for x in (0,1):
            state=ta[x^fb],tb[x]
            if state not in order:
                if len(order)>=LIMIT:raise RuntimeError('state-count cap')
                order[state]=len(order);queue.append(state)
            dest.append(order[state])
        out.append((fa^fb,tuple(dest)))
    return out

def minimize(machine):
    labels=[x[0] for x in machine];rounds=0
    while True:
        table={};new=[]
        for f,t in machine:
            key=f,labels[t[0]],labels[t[1]]
            if key not in table:table[key]=len(table)
            new.append(table[key])
        rounds+=1
        if new==labels:break
        labels=new
    reps={}
    for i,label in enumerate(labels):reps.setdefault(label,i)
    out=[]
    for label in range(len(reps)):
        f,t=machine[reps[label]];out.append((f,(labels[t[0]],labels[t[1]])))
    return reroot(out,labels[0]),rounds

def main():
    rng=random.Random(307029);report={'derived_states':BASE,'records':[],
        'finite_experiments_only':True,'full_problem_solved':False};start=time.monotonic()
    for name,root in [('Phi',0),('front_F',1)]:
        machine=reroot(BASE,root);power=1
        for stage in range(12):
            before=time.monotonic();machine,rounds=minimize(machine);checks=0
            for n in (1,2,7,16,32,64):
                for _ in range(32):
                    a=rng.getrandbits(n);b=a
                    for _ in range(power):b=phi(b)^(name=='front_F')
                    assert run(machine,a,n)==b&((1<<n)-1);checks+=1
            row={'map':name,'power':power,'minimal_reachable_states':len(machine),
                 'refinement_rounds':rounds,'integer_controls':checks,
                 'seconds':round(time.monotonic()-before,3)}
            report['records'].append(row);save('mealy-probe.json',report);print(row,flush=True)
            if time.monotonic()-start>100:break
            try:machine=compose(machine,machine)
            except RuntimeError as exc:
                report['records'].append({'map':name,'next_power':2*power,'stopped':str(exc)});break
            power*=2
    report['seconds']=round(time.monotonic()-start,3);save('mealy-probe.json',report)

if __name__=='__main__':main()
