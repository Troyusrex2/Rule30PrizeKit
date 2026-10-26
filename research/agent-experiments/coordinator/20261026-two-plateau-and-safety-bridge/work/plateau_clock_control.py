"""Check whether a proposed plateau lemma relied on a common clock."""
from pathlib import Path
import json,sys,time
sys.path.insert(0,r'D:\MWB\Rule30\toolchain\python-research')
import z3
root=Path(__file__).resolve().parent
results=[]
for R in [2,4,8,16]:
    for multiplier in [2,4,8]:
        T=multiplier*R;width=7
        solver=z3.Solver();solver.set(timeout=6000,max_memory=1024,random_seed=1512)
        x=[z3.BitVec(f'x{j}',T) for j in range(width)]
        for j in range(2,width):
            solver.add(z3.RotateRight(x[j],1)==x[j]^(x[j-1]|x[j-2]))
        # Oldest -> newest: [n,m,l,k,h,g] plus one more old profile.
        source=width-3
        solver.add(z3.RotateRight(x[source],R)==~x[source])
        solver.add(z3.RotateRight(x[source-1],R)==x[source-1])
        solver.add(x[-1]|x[-2]==(1<<T)-1)
        start=time.monotonic();answer=solver.check()
        result={'R':R,'clock':T,'width':width,'status':str(answer),
                'seconds':time.monotonic()-start,'timeout_ms':6000}
        if answer==z3.sat:
            model=solver.model();values=[model.eval(v,model_completion=True).as_long() for v in x]
            for t in range(T):
                row=[(v>>t)&1 for v in values]
                for j in range(2,width):
                    assert (values[j]>>((t+1)%T))&1==row[j]^(row[j-1]|row[j-2])
                assert row[-1]|row[-2]==1
                assert ((values[source]>>((t+R)%T))&1)==1-row[source]
                assert ((values[source-1]>>((t+R)%T))&1)==row[source-1]
            result['profiles_oldest_to_newest']=values
            result['literal_audit']=True
        if answer==z3.unknown:result['reason']=solver.reason_unknown()
        results.append(result)
        print(json.dumps({k:v for k,v in result.items() if k!='profiles_oldest_to_newest'}),flush=True)
        (root/'plateau-clock-control.json').write_text(json.dumps({'results':results,
            'scope':'finite cyclic relaxation, oldest two arbitrary; no actual white ancestry',
            'uniform_lemma_proved':False},indent=2)+'\n',encoding='utf-8')
