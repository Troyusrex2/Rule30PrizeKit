"""Pure Python replay of every finite-DFA rejection witness, without Numba."""
from pathlib import Path
import json,time
from profile_data import literal,C
r=Path(__file__).resolve().parent;t=time.monotonic()
j=json.loads((r/'temporal-dfa-probe.json').read_bytes());data=j['samples'];tables=0
for d in data:
    literal(d);q=0
    for b in d['parent_initial']+[0]:q=C[q][b]
    assert q in {0,1,2,3,5}
for S in range(1,5):
    certificates=j['counterexample_pairs_by_table'][str(S)]
    assert len(certificates)==S**(2*S)
    for table in range(S**(2*S)):
        v=table;trans=[]
        for _ in range(2*S):trans.append(v%S);v//=S
        a,b=certificates[str(table)];assert data[a]['target']!=data[b]['target']
        def final(d):
            state=0
            for t in range(d['clock']):state=trans[2*state+((d['OR_profile']>>t)&1)]
            return state
        assert final(data[a])==final(data[b]),(S,table)
        tables+=1
out={'passed':True,'finite_profiles':len(data),'transition_tables_independently_checked':tables,
 'maximum_clock':max(d['clock'] for d in data),'all_initial_words_canonical':True,
 'literal_cycle_profiles_checked':True,'Numba_used_for_audit':False,'Lean_verified':False,
 'full_observer_refuted':False,'full_problem_solved':False,'seconds':round(time.monotonic()-t,3)}
(r/'temporal-dfa-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
