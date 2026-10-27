from pathlib import Path
import json, hashlib, time

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'cut31-local-event-map-20261027T0840'
started = time.perf_counter()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
input_hashes = {n:sha(SOURCE/n) for n in ('PROTOCOL.md','probe.py','RESULT.json')}
saved = json.loads((SOURCE/'RESULT.json').read_text(encoding='utf-8'))
assert saved['source_sha256'] == input_hashes['probe.py']

# Event positions, not the author's packed countdown recursion.
# f is the first black site in [0,infinity); g is its incoming gap.
word_witnesses = {}
def extend(events, last_gap, first, incoming):
    if events[-1] > 16:
        bits = tuple(int(i in events) for i in range(17))
        word_witnesses.setdefault(bits, {'first_black':first,'incoming_gap':incoming,
                                       'events_through_first_after_window':events})
        return
    for gap in (3,5):
        if last_gap == gap == 3: continue
        extend(events+[events[-1]+gap],gap,first,incoming)

for first in range(5):
    for incoming in (3,5):
        if first < incoming:
            extend([first],incoming,first,incoming)

def pack(bits): return sum(b*(2**i) for i,b in enumerate(bits))
assert len(word_witnesses) == 26
assert {pack(b) for b in word_witnesses} == {r['word'] for r in saved['records']}

# Explicit independent finite graph reachability verification.
states = {(d,g) for g in (3,5) for d in range(g)}
edges = {}
for d,g in states:
    edges[d,g] = {(d-1,g)} if d else {(h-1,h) for h in (3,5) if (g,h)!=(3,3)}
for start in states:
    reached, todo = set(), [start]
    while todo:
        state = todo.pop()
        if state in reached: continue
        reached.add(state); todo.extend(edges[state])
    assert reached == states

# Literal physical Rule30 table, indexed by (left,center,right).
table = (0,1,1,1,1,0,0,0)
def left_from(output,center,right):
    choices = [left for left in (0,1) if table[4*left+2*center+right] == output]
    assert len(choices)==1
    return choices[0]

records = []
stencils = 0
root_by_word = {r['word']:r for r in saved['records']}
for g in sorted(word_witnesses, key=pack):
    a = [1-g[t//2] if t%2==0 else 1 for t in range(33)]
    columns = [[0]*33,a]
    for depth in range(2,33):
        right,current = columns[-2:]
        columns.append([left_from(current[i+1],current[i],right[i])
                        for i in range(len(current)-1)])
        stencils += len(columns[-1])
    actual_b = columns[32][:2]
    actual_l = [columns[31][i]*(1-columns[32][i]) for i in (0,1)]
    k = [g[i]*g[i+3] for i in range(14)]
    xor = lambda indices: sum(k[i] for i in indices)%2
    isolated_b = [(1+g[1]+xor([1,5,7,8,12]))%2,
                  (1+xor([3,4,7,8,11,13]))%2]
    isolated_l = [xor([6,7,12]),xor([7,8,13])]
    predicted_b = [isolated_b[0],(isolated_b[1]+k[4]*k[12])%2]
    predicted_l = [isolated_l[0],(isolated_l[1]+k[5]*k[13])%2]
    assert actual_b == predicted_b and actual_l == predicted_l
    root = root_by_word[pack(g)]
    assert (pack(actual_b),pack(actual_l)) == (root['B'],root['L'])
    assert (pack(isolated_b),pack(isolated_l)) == (root['isolated_B'],root['isolated_L'])
    residual = pack([(actual_b[i]+isolated_b[i])%2 for i in (0,1)] +
                    [(actual_l[i]+isolated_l[i])%2 for i in (0,1)])
    features = [i for i in range(6) if k[i]*k[i+8]]
    assert residual == root['residual'] and features == root['features']
    records.append({'word':pack(g),'gate_bits':list(g),
                    'extension_witness':word_witnesses[g],
                    'B':actual_b,'L':actual_l,
                    'odd_corrections':[k[4]*k[12],k[5]*k[13]],
                    'isolated_residual':residual})
assert all(input_hashes[n]==sha(SOURCE/n) for n in input_hashes)
out={'status':'INDEPENDENT_LANGUAGE_AND_LITERAL_SCALAR_PASS',
     'input_sha256':input_hashes,'automaton_states':8,'strongly_connected':True,
     'distinct_length17_words':len(records),'literal_scalar_inversions':stencils,
     'physical_rule_table':list(table),'records':records,
     'elapsed_seconds':time.perf_counter()-started,
     'scope':'Exact finite local-function audit plus separately written language/locality proof; no Lean claim, trajectory, or transformed-class closure.'}
(HERE/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ('status','automaton_states','strongly_connected','distinct_length17_words','literal_scalar_inversions','elapsed_seconds')}))
