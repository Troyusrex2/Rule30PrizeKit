"""Probe the last CEGAR candidate and examine independently replayed finite starts."""
from pathlib import Path
import hashlib,json,sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root/'solver-deps'))
import z3
data=json.loads((root/'coupled-language-cegar.json').read_text())['rounds'][-1]['candidate']
prefix=list(map(int,data['prefix_bits']));first=data['tail_first']
f=prefix+[first^(j%2) for j in range(256-len(prefix))]
started=time.monotonic();records=[]
for n in [32,40,48,56,64,80,96,128]:
    start=time.monotonic();s=z3.Solver();s.set(timeout=12000,random_seed=303025)
    initial=[z3.BoolVal(True)]+[z3.Bool('r_'+str(p)) for p in range(1,2*n+1)];row=initial
    for t in range(2*n-1):
        new=[z3.BoolVal((t+1)%2==0)]
        for p in range(1,len(row)-1):
            b=z3.Bool('c_'+str(t+1)+'_'+str(p));new.append(b)
            s.add(b==z3.Xor(row[p-1],z3.Or(row[p],row[p+1])))
        row=new
        if t%2==0:s.add(row[1]==bool(1-f[t//2]))
    r=s.check();rec={'requested_free_prefix':n,'maximum_initial_position':2*n,'result':str(r),'seconds':time.monotonic()-start}
    if r==z3.unknown:rec['reason']=s.reason_unknown()
    if r==z3.sat:
        model=s.model();code=sum(int(z3.is_true(model.eval(initial[p],model_completion=True)))<<p for p in range(1,len(initial)))
        row=code|1;actual=[];physical={0}|{p for p in range(1,len(initial)) if code>>p&1};other=[]
        for t in range(2*n-1):
            row=((row<<1)^(row|(row>>1)))&~1
            physical={p for p in range(1,max(physical|{1})+2) if int(p-1 in physical)^(int(p in physical)|int(p+1 in physical))}
            if t%2:row|=1;physical.add(0)
            else:actual.append(1-(row>>1&1));other.append(int(1 not in physical))
        assert actual==other==f[:n]
        row=code|1;extended=[]
        for t in range(2*5001-1):
            row=((row<<1)^(row|(row>>1)))&~1
            if t%2:row|=1
            else:extended.append(1-(row>>1&1))
        width=10000;cur=sum((1 if t%2==0 else extended[t//2])<<t for t in range(width+1));prev=0;psi=[0,cur&1]
        for k in range(2,width+1):
            prev,cur=cur,((cur>>1)^(cur|prev))&((1<<(width-k+2))-1)
            psi.append(cur&1)
        zeros=sum(1-b for b in extended[:5000]);black=sum(psi)
        mismatch=next((i for i in range(256) if extended[i]!=f[i]),None)
        tailperiod=next((p for p in range(1,129) if all(extended[i]==extended[i-p] for i in range(4000,5000))),None)
        rec.update({'mathematical_initial_right_hex':hex(code),'independent_physical_replay':True,
                    'first_target_mismatch_through256':mismatch,'finite_free_tail_period_candidate':tailperiod,
                    'finite_n':5000,'zeros':zeros,'blackPsi_2nplus1':black,'C3_excess':5*zeros-5000-3*black,
                    'free_first256':''.join(map(str,extended[:256]))})
    records.append(rec);print(json.dumps(rec),flush=True)
    if r!=z3.sat:break
out={'finite_only':True,'Lean_verified':False,'target':data,'records':records,
     'z3_version':z3.get_version_string(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'seconds':time.monotonic()-started,
     'scope':'Full finite causal cones, independent model replay, finite subsequent measurements. No eventual period or C3 asymptotic conclusion follows.'}
(root/'inverse-refined-candidate.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
