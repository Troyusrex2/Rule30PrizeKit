"""Exact finite-state minimization of recursive orbit sections.
Failure to close within a cap is UNKNOWN, never an infinite-state theorem.
"""
from pathlib import Path
from functools import lru_cache
import json,time,hashlib
root=Path(__file__).resolve().parent
# States A=0=(A,B), B=1=(C,B)swap, C=2=(A,B)swap.
NEXT=((0,1),(2,1),(0,1));FLIP=(0,1,1)
MAX_STATES=12000;MAX_AUT=500;MAX_WORD=32;SECONDS=120
start=time.monotonic()
@lru_cache(maxsize=100000)
def section(w,b):
    result=[]
    for q in w:
        result.append(NEXT[q][b]);b^=FLIP[q]
    return tuple(result)
def flip(w):return sum(FLIP[q] for q in w)%2
def action(w,x,n):
    y=0
    for j in range(n):
        b=(x>>j)&1;y|=(b^flip(w))<<j;w=section(w,b)
    return y
def canonical(w):
    states=[w];ids={w:0};rows=[];at=0
    while at<len(states):
        if len(states)>MAX_STATES:return None,{'status':'section_state_cap','discovered':len(states)}
        if time.monotonic()-start>SECONDS:return None,{'status':'time_cap','discovered':len(states)}
        row=[flip(states[at])]
        for b in (0,1):
            s=section(states[at],b)
            if s not in ids:ids[s]=len(states);states.append(s)
            row.append(ids[s])
        rows.append(row);at+=1
    classes=[r[0] for r in rows]
    while True:
        keys=[(r[0],classes[r[1]],classes[r[2]]) for r in rows]
        code={k:i for i,k in enumerate(sorted(set(keys)))};new=[code[k] for k in keys]
        if new==classes:break
        # Partitions only refine; equal class counts imply stability despite relabeling.
        stable=len(set(new))==len(set(classes));classes=new
        if stable:break
    representatives={c:i for i,c in enumerate(classes)}
    todo=[classes[0]];number={todo[0]:0};result=[]
    for c in todo:
        row=rows[representatives[c]];out=[row[0]]
        for k in (1,2):
            child=classes[row[k]]
            if child not in number:number[child]=len(todo);todo.append(child)
            out.append(number[child])
        result.append(out)
    key=json.dumps(result,separators=(',',':'))
    return key,{'status':'complete','unminimized_states':len(states),'minimal_states':len(result)}
controls=0
for n in range(13):
    mask=(1<<n)-1
    for x in range(1<<n):
        expected=(x^((x<<1)|(x<<2)))&mask
        assert action((0,),x,n)==expected;controls+=1
for m in range(1,9):
    for x in [0,1,3,0x555,0x7ab,0xfff]:
        expected=x
        for _ in range(m):expected=(expected^((expected<<1)|(expected<<2)))&4095
        assert action((0,)*m,x,12)==expected;controls+=1
w=(0,);key,info=canonical(w);autos=[w];keys={key:0};reports=[];edges=[];at=0;stop=None
while at<len(autos):
    if len(autos)>MAX_AUT:stop={'status':'automorphism_cap'};break
    w=autos[at];children=[]
    word=w+w if flip(w) else w
    if len(word)>MAX_WORD:stop={'status':'word_length_cap','parent':at,'required_length':len(word)};break
    for b in (0,1):
        child=section(word,b);ck,ci=canonical(child)
        if ck is None:stop={**ci,'parent':at,'input':b,'word_length':len(child)};break
        if ck not in keys:keys[ck]=len(autos);autos.append(child)
        children.append(keys[ck])
    if stop:break
    rec={'node':at,'word':''.join('ABC'[q] for q in w),'word_length':len(w),'root_flip':flip(w),
         'children':children,'canonical_sha256':hashlib.sha256(key.encode()).hexdigest() if at==0 else None}
    reports.append(rec);edges.append(children);print(json.dumps(rec),flush=True);at+=1
result={'controls':controls,'processed':at,'discovered':len(autos),'closed':stop is None,
        'stop':stop,'nodes':reports,'unprocessed_words':[''.join('ABC'[q] for q in w) for w in autos[at:]],
        'seconds':round(time.monotonic()-start,3),'Lean_verified':False,'infinite_signalizer_proved':False,
        'reader_completeness_proved':False,'full_problem_solved':False}
(root/'orbit-sections.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k not in ['nodes','unprocessed_words']}),flush=True)
