"""Locate a local obstruction or counterexample for longer plateau chains."""
from pathlib import Path
import json,sys,time
r=Path(__file__).resolve().parent
deps=Path.home()/'Rule30-offload/research/temporal-decoder-20261026/solver-deps'
if not deps.exists():deps=Path(r'D:\MWB\Rule30\toolchain\python-research')
sys.path.insert(0,str(deps));import z3
reports=[];start=time.monotonic()
for distance in [1,2,3,4]:
    for R in [2,4,8]:
        T=2*R;width=distance+5
        s=z3.Solver();s.set(timeout=8000,max_memory=1536,random_seed=1409)
        field=[z3.BitVec(f'x{j}',T) for j in range(width)]
        for j in range(2,width):s.add(z3.RotateRight(field[j],1)==field[j]^(field[j-1]|field[j-2]))
        # source at distance1 is h, at distance2 is k, etc.
        source=width-1-distance
        s.add(z3.RotateRight(field[source],R)==~field[source])
        s.add(z3.RotateRight(field[source-1],R)==field[source-1])
        s.add(field[-1]|field[-2]==z3.BitVecVal((1<<T)-1,T))
        t=time.monotonic();ans=s.check();out={'distance_from_g_to_antiperiodic_source':distance,
          'source_half_clock':R,'cyclic_clock':T,'strip_width':width,'status':str(ans),
          'solver_timeout_ms':8000,'seconds':round(time.monotonic()-t,3)}
        if ans==z3.sat:
            model=s.model();values=[model.eval(x,model_completion=True).as_long() for x in field]
            for t in range(T):
                for j in range(2,width):
                    bits=[x>>t&1 for x in values]
                    assert (values[j]>>((t+1)%T)&1)==((30>>(4*bits[j]+2*bits[j-1]+bits[j-2]))&1)
                assert (values[-1]>>t&1)|(values[-2]>>t&1)==1
            out['profiles_oldest_to_newest']=values;out['literal_checked']=True
        elif ans==z3.unknown:out['reason_unknown']=s.reason_unknown()
        reports.append(out);print(json.dumps({k:v for k,v in out.items() if k!='profiles_oldest_to_newest'}),flush=True)
        (r/'constant-or-plateau-sat.json').write_text(json.dumps({'reports':reports,
          'oldest_two_inputs_arbitrary':True,'finite_white_ancestry_established':False,
          'Lean_verified':False,'uniform_plateau_exclusion_proved':False,
          'full_problem_solved':False,'seconds':round(time.monotonic()-start,3)},indent=2)+'\n')
