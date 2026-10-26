"""Literal finite orbit/partition checks, independent of the JIT cycle algorithm."""
from pathlib import Path
import json,itertools,numpy as np
r=Path(__file__).resolve().parent
reader=json.loads((r/'learned-reader.json').read_bytes())['dfa'];T=reader['transitions'];A=set(reader['accepting'])
reports=json.loads((r/'orbit-partition.json').read_bytes())['reports'];pairs=0;cells=0
def read(x,y,n):
    q=0
    for j in range(n):q=T[q][2*((x>>j)&1)+((y>>j)&1)]
    return q in A
for n in range(1,9):
    N=1<<n;P=N;profiles=[]
    for initial in range(N):
        row=[(initial>>j)&1 for j in range(n)];bits=[]
        for _ in range(P):
            bits.append(row[-1])
            row=[(30>>((row[j]<<2)|((row[j-1] if j else 0)<<1)|(row[j-2] if j>1 else 0)))&1 for j in range(n)]
            cells+=n
        assert row==[(initial>>j)&1 for j in range(n)]
        profiles.append(tuple(bits))
    reps=json.loads((r/f'partition-representatives-{n}.json').read_bytes())
    assert all(profiles[x]==profiles[y] and read(x,y,n) for x,y in enumerate(reps))
    assert len(set(profiles))==reports[n-1]['distinct_column_profiles']
    for x in range(N):
        for y in range(N):
            assert (profiles[x]==profiles[y])==read(x,y,n);pairs+=1
source=(r/'orbit_partition.py').read_text(encoding='utf-8')
ns={'__file__':str(r/'orbit_partition.py')};exec(source.split('reports=[];counter=None;')[0],ns)
necklaces=0
for n in range(1,13):
    for word in itertools.product([0,1],repeat=n):
        p=ns['booth'](np.array(word,dtype=np.uint8),n)
        rotations=[word[k:]+word[:k] for k in range(n)]
        assert rotations[p]==min(rotations);necklaces+=1
out={'passed':True,'literal_cells_checked':cells,'all_pair_comparisons_through_width8':pairs,
     'minimal_rotation_controls':necklaces,'exact_comparisons_not_probabilistic_hashes':True,
     'Lean_verified':False,'all_width_completeness_proved':False,'full_problem_solved':False}
(r/'orbit-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out),flush=True)
