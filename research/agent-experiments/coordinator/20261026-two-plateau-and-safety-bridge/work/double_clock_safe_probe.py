from pathlib import Path
import json,sys,time
sys.path.insert(0,r'D:\MWB\Rule30\toolchain\python-research')
import z3
root=Path(__file__).resolve().parent;results=[]
for R in [1,2,4,8,16]:
    for old_R in [False,True]:
        T=4*R;s=z3.Solver();s.set(timeout=5000,max_memory=1024,random_seed=1558)
        x=[z3.BitVec('x'+str(j),T) for j in range(6)]
        for j in range(2,6):s.add(z3.RotateRight(x[j],1)==x[j]^(x[j-1]|x[j-2]))
        s.add(z3.RotateRight(x[2],R)==x[2],z3.RotateRight(x[3],R)==~x[3],
              z3.RotateRight(x[4],2*R)==~x[4])
        s.add(x[5]|x[4]|x[3]==(1<<T)-1)
        if old_R:
            for j in [0,1]:s.add(z3.RotateRight(x[j],R)==x[j])
        start=time.monotonic();ans=s.check()
        result={'R':R,'clock':T,'oldest_profiles_R_periodic':old_R,
                'status':str(ans),'seconds':time.monotonic()-start}
        if ans==z3.sat:
            values=[s.model().eval(v,model_completion=True).as_long() for v in x]
            for t in range(T):
                row=[(v>>t)&1 for v in values]
                for j in range(2,6):
                    assert ((values[j]>>((t+1)%T))&1)==row[j]^(row[j-1]|row[j-2])
                assert row[-1] or ((values[-1]>>((t+1)%T))&1)
            result['profiles']=values;result['literal_audit']=True
        elif ans==z3.unknown:result['reason']=s.reason_unknown()
        results.append(result)
        print(json.dumps({k:v for k,v in result.items() if k!='profiles'}),flush=True)
        (root/'double-clock-safe-probe.json').write_text(json.dumps({'results':results,
            'scope':'six-cell cyclic relaxation; oldest two arbitrary periodic inputs, NOT a full finite-white prefix',
            'all_width_or_prize_claim':False},indent=2)+'\n',encoding='utf-8')
