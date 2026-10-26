"""Try an all-width regular rank for unary no-00 traces.

The language is constructed from the already sound 17-state reader and
eleven explicitly checked reference traces. LP feasibility is checked
exactly; no numerical or bounded-width result is treated as a theorem.
"""
from pathlib import Path
from collections import deque
from fractions import Fraction
import ast,hashlib,json,math,re,sys,time
r=Path(__file__).resolve().parent
source=r/'Rule30ColumnReaderResearch.lean'
if not source.exists():source=Path(r'D:\MWB\Rule30\overnight-20261024\research\agent-experiments\coordinator\20261026-clock-search-mode-observer\work\Rule30ColumnReaderResearch.lean')
text=source.read_text(encoding='utf-8')
reader=ast.literal_eval(re.search(r'def table[^\n]*:= (\[\[.*\]\])',text).group(1))
acceptR={0,3,12,16}
reference=[15,49,23,41,31,33,39,57,16,48,32]
patterns=[]
for value in reference:
    p=(value&-value).bit_length()-1
    patterns.append(tuple(value>>j&1 for j in range(p,6)))
prefixes={()}
for w in patterns:
    for j in range(1,len(w)+1):prefixes.add(w[:j])
prefixes=sorted(prefixes,key=lambda x:(len(x),x));pi={x:i for i,x in enumerate(prefixes)};sink=len(prefixes)
target=[]
for p in prefixes:
    target.append([0 if not p and x==0 else pi.get(p+(x,),sink) for x in [0,1]])
target.append([sink,sink]);acceptT={pi[p] for p in patterns}
subsets=[frozenset({(0,0)})];index={subsets[0]:0};table=[];accept=[]
for subset in subsets:
    accept.append(any(q in acceptR and t in acceptT for q,t in subset));row=[]
    for x in [0,1]:
        nxt=frozenset((reader[q][2*x+y],target[t][y]) for q,t in subset for y in [0,1])
        if nxt not in index:index[nxt]=len(subsets);subsets.append(nxt)
        row.append(index[nxt])
    table.append(row)
classes=[int(x) for x in accept]
while True:
    sig=[(accept[q],classes[row[0]],classes[row[1]]) for q,row in enumerate(table)]
    uniq={x:i for i,x in enumerate(dict.fromkeys(sig))};new=[uniq[x] for x in sig]
    if new==classes:break
    classes=new
reps={}
for q,c in enumerate(classes):reps.setdefault(c,q)
order=[classes[0]];ren={order[0]:0};minimal=[];accepted=[]
for c in order:
    q=reps[c];accepted.append(accept[q]);row=[]
    for x in [0,1]:
        d=classes[table[q][x]]
        if d not in ren:ren[d]=len(order);order.append(d)
        row.append(ren[d])
    minimal.append(row)
counts=[];vector=[0]*len(minimal);vector[0]=1
for w in range(27):
    counts.append(sum(n for n,yes in zip(vector,accepted) if yes))
    nxt=[0]*len(minimal)
    for q,n in enumerate(vector):
        for x in [0,1]:nxt[minimal[q][x]]+=n
    vector=nxt
assert counts[6]==27 and counts[26]==267
# Coupled prefixes remember the three newest raw bits and length up to3.
states=[(0,0,0,0)];ids={states[0]:0};edges=[]
for q,qn,last,length in states:
    row=[]
    for x in [0,1]:
        y=x^((last&1)|((last>>1)&1))
        nxt=(minimal[q][x],minimal[qn][y],((last<<1)|x)&7,min(3,length+1))
        if nxt not in ids:ids[nxt]=len(states);states.append(nxt)
        row.append((ids[nxt],x,y))
    edges.append(row)
assert all(accepted[q]==accepted[qn] for q,qn,last,length in states)
targets=[i for i,(q,qn,last,length) in enumerate(states) if length==3 and last!=0 and not accepted[q]]
meta={'reader_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
      'reference_six_bit_words':reference,'reference_trimmed_patterns':[list(w) for w in patterns],
      'subset_states':len(subsets),'dfa_states':len(minimal),'table':minimal,'accept':accepted,
      'word_counts_by_width_0_to_26':counts,'coupled_states':[list(x) for x in states],
      'coupled_edges':edges,'strict_rank_terminal_states':targets,
      'acceptance_time_invariance_finitely_checked':True,'complete_all_width_language_proved':False}
(r/'safe-language-machine.json').write_text(json.dumps(meta,indent=2)+'\n')
deps=Path.home()/'Rule30-offload/research/temporal-decoder-20261026/solver-deps'
if not deps.exists():deps=Path(r'D:\MWB\Rule30\toolchain\python-research')
sys.path.insert(0,str(deps));import z3
s=z3.Solver();s.set(timeout=8000,max_memory=1536)
weights=[[z3.Real(f'w{q}_{x}') for x in range(2)] for q in range(len(minimal))]
pot=[z3.Real(f'p{i}') for i in range(len(states))];s.add(pot[0]==0)
for i,(q,qn,last,length) in enumerate(states):
    for j,x,y in edges[i]:s.add(weights[qn][y]-weights[q][x]+pot[i]-pot[j]>=0)
for i in targets:s.add(pot[i]>=1)
t=time.monotonic();ans=s.check()
out={'status':str(ans),'solver_timeout_ms':8000,'seconds':round(time.monotonic()-t,3),
     'dfa_states':len(minimal),'coupled_states':len(states),'strict_terminals':len(targets),
     'new_uniform_theorem_proved':False,'full_problem_solved':False}
if ans==z3.sat:
    model=s.model()
    def fraction(v):
        a=model.eval(v,model_completion=True);return Fraction(a.numerator_as_long(),a.denominator_as_long())
    w=[[fraction(v) for v in row] for row in weights];p=[fraction(v) for v in pot]
    assert p[0]==0
    for i,(q,qn,last,length) in enumerate(states):
        for j,x,y in edges[i]:assert w[qn][y]-w[q][x]+p[i]-p[j]>=0
    assert all(p[i]>=1 for i in targets)
    scale=math.lcm(*(v.denominator for row in w for v in row),*(v.denominator for v in p))
    out['exact_rational_audit_passed']=True;out['integer_weights']=[[int(v*scale) for v in row] for row in w]
    out['integer_potentials']=[int(v*scale) for v in p];out['strict_margin']=scale
elif ans==z3.unknown:out['reason_unknown']=s.reason_unknown()
(r/'safe-language-rank.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if not k.startswith('integer_')}))
