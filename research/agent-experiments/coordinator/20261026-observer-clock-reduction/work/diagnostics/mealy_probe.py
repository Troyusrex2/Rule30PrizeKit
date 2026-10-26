"""Exact finite-state equality of short positive words in the Rule 30 transducer.
Closed under sections: refinement to a fixed point decides equality on ALL
finite input words for this bounded generator-word set. Not a Lean result.
"""
from pathlib import Path
import itertools,json,time
r=Path(__file__).resolve().parent;begin=time.monotonic()
flip=[0,1,1];transition=[(0,2),(0,2),(1,2)]
def parts(w):
    answer=[]
    for x in range(2):
        bit=x;section=[0]*len(w)
        for i in range(len(w)-1,-1,-1):
            q=w[i];section[i]=transition[q][bit];bit^=flip[q]
        answer.append(tuple(section))
    return sum(flip[q] for q in w)%2,*answer
def action(w,xs):
    out=list(xs)
    for q in reversed(w):
        state=q;bits=[]
        for x in out:bits.append(x^flip[state]);state=transition[state][x]
        out=bits
    return out
def literal(q,xs):
    p,older=[(0,0),(0,1),(1,0)][q];out=[]
    for x in xs:
        out.append((30>>(4*x+2*p+older))&1);older,p=p,x
    return out
controls=0
for length in range(5):
  for w in itertools.product(range(3),repeat=length):
    f,s0,s1=parts(w)
    for n in range(1,7):
      for xs in itertools.product(range(2),repeat=n):
        direct=list(xs)
        for q in reversed(w):direct=literal(q,direct)
        assert action(w,xs)==direct
        assert direct==[xs[0]^f]+action(s1 if xs[0] else s0,xs[1:])
        controls+=1
# Include all shorter words as well so unequal lengths can be compared.
words=[w for length in range(9) for w in itertools.product(range(3),repeat=length)]
index={w:i for i,w in enumerate(words)}
decomposed=[parts(w) for w in words]
edges=[(index[p[1]],index[p[2]]) for p in decomposed];roots=[p[0] for p in decomposed]
groups=roots;history=[]
for depth in range(1,40):
    ids={};new=[]
    for i,(a,b) in enumerate(edges):
        key=(roots[i],groups[a],groups[b])
        if key not in ids:ids[key]=len(ids)
        new.append(ids[key])
    history.append({'input_depth':depth+1,'classes':len(ids)})
    if len(set(groups))==len(ids):groups=new;break
    groups=new
else:raise AssertionError('No fixed point reached')
classes={}
for i,g in enumerate(groups):classes.setdefault(g,[]).append(i)
relations=[]
for cls in classes.values():
    if len(cls)>1:
        best=words[cls[0]]
        for i in cls[1:]:
            relations.append({'left':''.join('abc'[x] for x in words[i]),'right':''.join('abc'[x] for x in best)})
def reduce(w):
    # Only replacements certified by the complete closed bounded automaton.
    reps={words[i]:words[cls[0]] for cls in classes.values() for i in cls}
    changed=True
    while changed:
        changed=False
        for size in range(min(8,len(w)),0,-1):
            for i in range(len(w)-size+1):
                v=reps[w[i:i+size]]
                if (len(v),v)<(size,w[i:i+size]):
                    w=w[:i]+v+w[i+size:];changed=True;break
            if changed:break
    return w
# Return sections for prefix100 have initial ca; root-flip section squares.
types={(2,0)};portrait=[]
for depth in range(9):
    portrait.append({'suffix_depth':depth,'return_types':len(types),'maximum_word_length':max(map(len,types))})
    nt=set()
    for w in types:
        f,a,b=parts(w)
        if f:nt.update([reduce(b+a),reduce(a+b)])
        else:nt.update([reduce(a),reduce(b)])
    if len(nt)>5000 or max(map(len,nt))>2048:break
    types=nt
out={'passed':True,'literal_and_section_controls':controls,'bounded_composition_length':8,
     'closed_automaton_states':len(words),'refinement_history':history,
     'complete_fixed_point':True,'global_action_classes_within_bound':len(classes),
     'relations':relations,'canonical_return_portrait':portrait,
     'seconds':round(time.monotonic()-begin,3),'Lean_verified':False,
     'all_length_word_freeness_proved':False,'canonical_observer_proved':False,'full_problem_solved':False}
(r/'mealy-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='relations'}),flush=True)
print(json.dumps({'relation_count':len(relations),'first_relations':relations[:12]}),flush=True)
