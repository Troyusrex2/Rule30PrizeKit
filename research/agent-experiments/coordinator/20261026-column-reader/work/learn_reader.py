"""L* pilot for exact temporal-column equality, with bounded equivalence tests.
Any output automaton is a conjecture until a separate unbounded proof exists.
"""
from pathlib import Path
from functools import lru_cache
import itertools,json,random,time
ROOT=Path(__file__).resolve().parent
ALPHABET=range(4);MAX_LENGTH=18;MAX_SECONDS=90;MAX_QUERIES=200000
start=time.monotonic();calls=0
class Incomplete(Exception):pass

def repeat(x,old,new):
    while old<new:x|=x<<old;old*=2
    return x
@lru_cache(maxsize=16000)
def column(bits,n):
    if not n:return 0
    P=1<<(n-1);mask=(1<<P)-1
    a=repeat(column(bits&((1<<(n-1))-1),n-1),P//2,P) if n>=2 else 0
    b=repeat(column(bits&((1<<(n-2))-1),n-2),P//4,P) if n>=3 else 0
    g=a|b;x=g;shift=1
    while shift<P:x^=x<<shift;shift*=2
    return ((x<<1)&mask)^(mask if bits>>(n-1)&1 else 0)

@lru_cache(maxsize=200000)
def member(word):
    global calls
    if len(word)>MAX_LENGTH:raise Incomplete('exact membership length limit')
    if time.monotonic()-start>MAX_SECONDS:raise Incomplete('pilot time limit')
    calls+=1
    if calls>MAX_QUERIES:raise Incomplete('membership query limit')
    a=sum(((v>>1)&1)<<j for j,v in enumerate(word));b=sum((v&1)<<j for j,v in enumerate(word))
    return column(a,len(word))==column(b,len(word))

def run(dfa,word):
    s=dfa['start']
    for a in word:s=dfa['transitions'][s][a]
    return s in dfa['accepting']
def paired(a,b,n):return tuple(((((a>>j)&1)<<1)|((b>>j)&1)) for j in range(n))

def equivalence(dfa,iteration):
    checked=0;positive=0
    for n in range(9):
        for word in itertools.product(ALPHABET,repeat=n):
            value=member(word);checked+=1;positive+=value
            if run(dfa,word)!=value:return word,{'kind':'exhaustive','checked':checked,'positives':positive,'length':n}
    rng=random.Random(302026+iteration)
    for i in range(6000):
        n=rng.randrange(9,17);a=rng.randrange(1<<n)
        kind=i%5
        if kind==0:b=rng.randrange(1<<n)
        elif kind==1:b=a
        elif kind==2:b=a^(1<<rng.randrange(n))
        elif kind==3:b=a^(1<<rng.randrange(n))^(1<<rng.randrange(n))
        else:
            a=(a&~7)|2;b=a^1
        word=paired(a,b,n);value=member(word);checked+=1;positive+=value
        if run(dfa,word)!=value:return word,{'kind':'heldout','checked':checked,'positives':positive,'length':n,'case':kind}
    return None,{'kind':'bounded_tests_passed','checked':checked,'positives':positive,'exhaustive_through':8,'heldout':6000}

# Scalar physical-prefix controls for the exact membership oracle.
control_count=0
for n in range(1,6):
    for a,b in itertools.product(range(1<<n),repeat=2):
        aa,bb=a,b;same=True
        for t in range(1<<(n-1)):
            same &= ((aa>>(n-1))&1)==((bb>>(n-1))&1)
            aa=aa^((aa<<1)|(aa<<2));bb=bb^((bb<<1)|(bb<<2))
        assert member(paired(a,b,n))==same;control_count+=1

S={()};E={()};history=[];last=None;stop='not_started';last_counterexample=None
def order(word):return len(word),word
try:
    for iteration in range(60):
        while True:
            eorder=sorted(E,key=order)
            def row(s):return tuple(member(s+e) for e in eorder)
            sorder=sorted(S,key=order);rows={row(s) for s in sorder}
            new=None
            for s in sorder:
                for a in ALPHABET:
                    if row(s+(a,)) not in rows:new=s+(a,);break
                if new is not None:break
            if new is not None:S.add(new);continue
            distinguisher=None
            for s,t in itertools.combinations(sorder,2):
                if row(s)!=row(t):continue
                for a in ALPHABET:
                    rs,rt=row(s+(a,)),row(t+(a,))
                    if rs!=rt:
                        i=next(i for i,(x,y) in enumerate(zip(rs,rt)) if x!=y)
                        distinguisher=(a,)+eorder[i];break
                if distinguisher is not None:break
            if distinguisher is not None:E.add(distinguisher);continue
            break
        representatives={}
        for s in sorted(S,key=order):representatives.setdefault(row(s),s)
        rep=list(representatives.values());index={row(s):i for i,s in enumerate(rep)}
        last={'start':index[row(())],'transitions':[[index[row(s+(a,))] for a in ALPHABET] for s in rep],
              'accepting':[i for i,s in enumerate(rep) if member(s)],'representatives':[list(s) for s in rep],
              'distinguishers':[list(e) for e in eorder]}
        if len(rep)>64:raise Incomplete('state limit')
        witness,evidence=equivalence(last,iteration)
        rec={'iteration':iteration,'states':len(rep),'prefixes':len(S),'distinguishers':len(E),'queries':calls,
             'counterexample':list(witness) if witness is not None else None,'equivalence':evidence}
        history.append(rec);print(json.dumps(rec),flush=True)
        if witness is None:stop='bounded_candidate';break
        last_counterexample=witness
        for i in range(len(witness)+1):S.add(witness[:i])
    else:stop='iteration_limit'
except Incomplete as e:stop=str(e)
out={'stop_reason':stop,'dfa':last,'history':history,'exact_membership_controls':control_count,'membership_queries':calls,
     'last_counterexample':list(last_counterexample) if last_counterexample is not None else None,
     'maximum_membership_length':MAX_LENGTH,'seconds':round(time.monotonic()-start,3),
     'finite_tests_only':True,'regularity_proved':False,'Lean_verified':False,'full_problem_solved':False,
     'alphabet':['00','01','10','11']}
(ROOT/'learned-reader.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['dfa','history']}),flush=True)
