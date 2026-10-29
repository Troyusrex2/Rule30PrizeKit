"""Exhaustive small-DFA oracle for the discovery CNF, without running a solver."""
from pathlib import Path
import ast,itertools,json,time
ROOT=Path(__file__).resolve().parent;tick=time.monotonic()
tree=ast.parse((ROOT/'probe.py').read_text());selected=[n for n in tree.body if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in ['CNF','encode']]
assert len(selected)==2
env={};exec(compile(ast.Module(body=selected,type_ignores=[]),'owned-discovery-encoder','exec'),env)
cases=[({(0,)},{(1,)},set()),({(0,)},{(1,)},{((0,),(1,))}),(set(),{(0,),(1,)},{((0,),(1,))})];counts=[]
for P,N,I in cases:
    env.update(positive=P,negative=N,implications=I);enc,delta,final,nodes=env['encode'](2)
    words=P|N|{w for pair in I for w in pair};prefixes=sorted({w[:k] for w in words for k in range(len(w)+1)},key=lambda p:(len(p),p));assert len(prefixes)==nodes
    accepted=0
    for bits in itertools.product((0,1),repeat=10):
        transitions=[list(bits[:4]),list(bits[4:8])];F={s for s in range(2) if bits[8+s]}
        def walk(word):
            state=0
            for symbol in word:state=transitions[state][symbol]
            return state
        expected=all(walk(w) in F for w in P) and all(walk(w) not in F for w in N) and all(walk(a) not in F or walk(b) in F for a,b in I)
        model={v:False for v in range(1,enc.n+1)}
        for s in range(2):
            for symbol in range(4):model[delta[s][symbol][transitions[s][symbol]]]=True
            model[final[s]]=s in F
        offset=4*2*2+2
        assert enc.n==offset+2*len(prefixes)
        for i,prefix in enumerate(prefixes):model[offset+2*i+walk(prefix)+1]=True
        actual=all(any(model[abs(v)]==(v>0) for v in clause) for clause in enc.clauses)
        assert actual==expected
        accepted+=actual
    counts.append(accepted)
assert counts[0]>0 and counts[1]==0 and counts[2]>0
out={'passed':True,'scope':'post-run exact encoder controls only; no second math search','dfa_assignments_checked':3072,'satisfying_counts':counts,'implication_not_unconditional_positive_checked':True,'seconds':time.monotonic()-tick}
(ROOT/'ENCODER-CONTROLS.json').write_bytes((json.dumps(out,indent=2)+'\n').encode());print(json.dumps(out))
