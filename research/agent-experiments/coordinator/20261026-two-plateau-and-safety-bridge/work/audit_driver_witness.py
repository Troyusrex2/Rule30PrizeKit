"""Independent scalar check of supplied walks; imports no graph builder."""
from pathlib import Path
import json

root=Path(__file__).resolve().parent
data=json.loads((root/'periodic-driver-witnesses.json').read_bytes())
records=[]
for result in data['results']:
    driver=list(map(int,result['driver']));width=result['width'];size=2**width
    loops=[]
    for key in ['loop_a','loop_b']:
        loop=result[key];nodes=loop['nodes'];outside=loop['outer_bits']
        assert nodes[0]==nodes[-1]==result['common_base']
        assert len(outside)==len(nodes)-1==loop['length']
        observed=[]
        for t,u in enumerate(outside):
            phase,state=divmod(nodes[t],size);phase2,state2=divmod(nodes[t+1],size)
            assert phase2==(phase+1)%len(driver)
            bits=[(state//(2**j))%2 for j in range(width)]
            next_bits=[]
            for j in range(width):
                left=driver[phase] if j==0 else bits[j-1]
                right=u if j+1==width else bits[j+1]
                next_bits.append(int(left != bool(bits[j] or right)))
            assert state2==sum(b*2**j for j,b in enumerate(next_bits))
            observed.append(int(bool(driver[phase] or bits[0])))
        assert observed==loop['outputs'];loops.append(observed)
    assert loops[0]+loops[1]!=loops[1]+loops[0]
    records.append({'driver':result['driver'],'width':width,
        'scalar_edges_checked':sum(len(x) for x in loops),
        'common_base_verified':True,'noncommuting_output_words_verified':True})
(root/'periodic-driver-witness-audit.json').write_text(json.dumps({'independent_literal_audit':records,
    'consequence':'arbitrary concatenations of the two equal-length AB/BA loops embed a binary output code in this finite free-boundary model',
    'not_claimed':['finite-start realization','all-width obstruction','Prize Problem 1']},indent=2)+'\n',encoding='utf-8')
print('Three loop witnesses independently verified, including every literal Rule 30 edge.')
