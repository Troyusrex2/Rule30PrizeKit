"""Independent certificate audit, plus deliberate corruption controls."""
from pathlib import Path
import copy,itertools,json
ROOT=Path(__file__).resolve().parent
obj=json.loads((ROOT/'word-tree-odd.json').read_bytes())
count=0
def audit(data):
    global count
    count=0
    def walk(node,known):
        global count
        count+=1;known=dict(known)
        for step in node['steps']:
            positions=[tuple(q) for q in step['relation']]
            (nt,p),(t,pl),(tb,pc),(tc,pr)=positions
            assert nt==t+1 and tb==tc==t and pl==p-1 and pc==p and pr==p+1
            assert all(known[tuple(q['cell'])]==q['value'] for q in step['premises'])
            target=tuple(step['cell']);assert target in positions and target not in known
            possibilities=[]
            for values in itertools.product([0,1],repeat=4):
                if values[0]!=(values[1]^(values[2]|values[3])):continue
                if any(q in known and known[q]!=values[i] for i,q in enumerate(positions)):continue
                possibilities.append(values[positions.index(target)])
            assert possibilities and set(possibilities)=={step['value']}
            known[target]=step['value']
        if 'conflict' in node:
            positions=[tuple(q) for q in node['conflict']]
            assert not any(v[0]==(v[1]^(v[2]|v[3])) and
                           all(q not in known or known[q]==v[i] for i,q in enumerate(positions))
                           for v in itertools.product([0,1],repeat=4))
        else:
            assert len(node['branches'])==2
            target=tuple(node['split']);assert target not in known
            for b,branch in enumerate(node['branches']):walk(branch,{**known,target:b})
    walk(data['tree'],{tuple(q['cell']):q['value'] for q in data['initial']})
    return count
assert audit(obj)==9
rejected=[]
bad=copy.deepcopy(obj);bad['tree']['steps'][0]['value']^=1
try:audit(bad)
except AssertionError:rejected.append('wrong_forced_value')
bad=copy.deepcopy(obj);bad['tree']['branches'].pop()
try:audit(bad)
except AssertionError:rejected.append('missing_boolean_branch')
assert len(rejected)==2
word='1010111010'
assert all(w not in word for w in ['00','11111','010110','1011010'])
for L in [6,8,10,18,100,4002]:
    def f(s):return int(s==L)^(s%2)
    assert ''.join(str(f(L-5+i)) for i in range(10))==word
out={'passed':True,'nodes':9,'corruptions_rejected':rejected,
     'word_not_excluded_by_previous_four_words':True,'finite_only':True,'Lean_verified':False}
(ROOT/'independent-tree-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
