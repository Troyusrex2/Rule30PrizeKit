from pathlib import Path
import hashlib,json,time
from fractions import Fraction
root=Path(__file__).resolve().parent
# Only definitions, with no search execution on import.
src=(root/'cyclic_preimages.py').read_text().split('# Exhaustive independent small-ring check')[0]
(root/'cyclic_core.py').write_text(src,encoding='utf-8')
from cyclic_core import rule_word,canonical
data=json.loads((root/'cyclic-depth.json').read_text())
words={hashlib.sha256(bytes(map(int,w))).hexdigest():w for w in data['bases']}
phase={h:int(w in ['0000001','0010011']) for h,w in words.items()}
records={};minima={};controls=0
for r in data['records']:
    parent=words[r['parent_sha256']]
    assert ''.join(map(str,canonical(rule_word(bytes(map(int,r['word']))))))==parent
    assert len(r['word'])==r['period'] and r['word'].count('1')==r['black']
    h=r['sha256'];assert h not in words
    assert h==hashlib.sha256(bytes(map(int,r['word']))).hexdigest()
    words[h]=r['word'];records[h]=r;phase[h]=phase[r['parent_sha256']]^1
    q=phase[h]
    if q not in minima or Fraction(r['density'])<Fraction(minima[q]['density']):minima[q]=r
    controls+=1
assert len(words)==50001 and max(map(len,words.values()))==112
path=[];r=minima[0]
while True:
    path.append(r);h=r['parent_sha256']
    if h not in records:
        rootword=words[h];break
    r=records[h]
assert len(path)==360 and minima[0]['density']=='5/28' and phase[h]==0
result={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
 'verified_parent_edges':controls,'nodes':len(words),'maximum_period':112,
 'minimum_including_bases':str(min(Fraction(w.count('1'),len(w)) for w in words.values())),
 'minimum_new_ancestors_by_temporal_parity':{str(q):r for q,r in minima.items()},
 'even_phase_witness_root':rootword,'even_phase_witness_path':path,
 'source_graph_sha256':hashlib.sha256((root/'cyclic-depth.json').read_bytes()).hexdigest(),
 'scope':'Cyclic whole-row predecessors, a superset of boundary-compatible Theta tails. Neither the 5/28 word nor its path is asserted to be an actual finite-right response or a valid Theta tail.'}
(root/'cyclic-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'nodes':len(words),'parent_edges_checked':controls,'period_max':112,
 'even_phase_minimum_new':minima[0]['density'],'witness_path':len(path),'not_a_Theta_certificate':True}))
