"""Validate the actual cyclic encoding and determine whether white-boundary clauses matter."""
from pathlib import Path
import json,sys,time
sys.path.insert(0,r'D:\MWB\Rule30\toolchain\python-research')
import z3
root=Path(__file__).resolve().parent
assertions=z3.parse_smt2_file(str(root/'query.smt2'))
assert len(assertions)==66
control=next(c for c in json.loads((root/'orientation-controls.json').read_bytes())['controls'] if c['word']=='10000001')
profiles=[0]*56+control['profiles'];assert len(profiles)==64
positive=z3.Solver();positive.set(timeout=60000)
positive.add(*assertions[:64]);positive.add(assertions[-1])
for j,v in enumerate(profiles):positive.add(z3.BitVec('column_'+str(j),32)==v)
start=time.monotonic();positive_result=positive.check();assert positive_result==z3.sat
positive_seconds=time.monotonic()-start
core=z3.Solver();core.set(timeout=60000,unsat_core=True)
for j,assertion in enumerate(assertions[:65]):core.assert_and_track(assertion,'actual_'+str(j) if j<64 else 'target')
start=time.monotonic();result=core.check();seconds=time.monotonic()-start
names=[str(t) for t in core.unsat_core()] if result==z3.unsat else []
indices=sorted(int(n.split('_')[1]) for n in names if n.startswith('actual_'))
out={'positive_control':'literal 10000001 preceded by 56 inert white cells','positive_result':str(positive_result),'positive_seconds':positive_seconds,'positive_whole_F8_failure_checked':True,'target_without_F8_failure':str(result),'seconds':seconds,'unsat_core_names':names,'actual_column_indices_in_core':indices,'white_boundary_clauses_used':any(j<2 for j in indices),'kernel_verified':False,'scope':'An unsat core identifies sufficient assertions for this fixed32-phase target; it is not a Lean proof or a general ancestry result.'}
(root/'query-audit.json').write_bytes((json.dumps(out,indent=2)+'\n').encode())
print(json.dumps({k:out[k] for k in ['positive_result','target_without_F8_failure','actual_column_indices_in_core','white_boundary_clauses_used','kernel_verified']}))
