"""One fixed P=32, seven-column local control; no width/clock sweep."""
from pathlib import Path
import sys,json,time
sys.path.insert(0,'D:/MWB/Rule30/wolfram-local/z3-deps')
import z3
root=Path(__file__).resolve().parent
P=32;names=['r','q','w','v','u','A','b']
x={name:[z3.Bool(f'{name}_{t}') for t in range(P)] for name in names}
s=z3.Solver();s.set(timeout=45000,random_seed=30)
for j in range(2,len(names)):
    c,a,u=(x[names[j-k]] for k in [0,1,2])
    for t in range(P):s.add(z3.Xor(c[t],c[(t+1)%P])==z3.Or(a[t],u[t]))
for j in range(1,len(names)):
    a,c=x[names[j-1]],x[names[j]]
    for t in range(P):
        d=z3.Xor(c[t],c[(t+1)%P])
        s.add(z3.Implies(a[t],d),z3.Implies(d,z3.Or(a[t],a[(t+1)%P])))
for name in names:
    for word in ['11011','00100','000111','111000']:
        for t in range(P):s.add(z3.Not(z3.And([x[name][(t+i)%P]==(ch=='1') for i,ch in enumerate(word)])))
h={}
for name in ['b','A','u']:
    h[name]=[z3.IntVal(0)]
    for t in range(P):h[name].append(h[name][-1]+((-1)**t)*z3.If(x[name][t],0,1))
lo=z3.Int('b_low');s.add(h['b'][-1]==0)
s.add([z3.And(lo<=v,v<=lo+2) for v in h['b']])
s.add(z3.Or([x['b'][t]!=x['b'][(t+8)%P] for t in range(P)]))
for name in ['A','u']:
    # Neither the parent nor its leaf complement is Safe.
    s.add(z3.Or([z3.And(x[name][t],x[name][(t+1)%P]) for t in range(P)]))
    s.add(z3.Or([z3.And(z3.Not(x[name][t]),z3.Not(x[name][(t+1)%P])) for t in range(P)]))
    mn,mx=z3.Ints(name+'_min '+name+'_max')
    s.add([mn<=v for v in h[name]]+[v<=mx for v in h[name]])
    s.add(z3.Or([mn==v for v in h[name]]),z3.Or([mx==v for v in h[name]]))
    s.add(z3.Or(h[name][-1]!=0,mx-mn>2))
start=time.monotonic();result=s.check()
out={'clock':P,'columns':len(names),'solver':z3.get_version_string(),'status':str(result),'seconds':time.monotonic()-start,
 'scope':'Free oldest pair; five shared actual update equations; all adjacent cover relations; four forbidden cylinders in every supplied column. No finite-white anchor.'}
if result==z3.sat:
    m=s.model();bits={name:[bool(z3.is_true(m.eval(z))) for z in x[name]] for name in names}
    profiles={}
    for name,word in bits.items():
        heights=[0]
        for t,c in enumerate(word):heights.append(heights[-1]+((-1)**t)*(not c))
        period=next(p for p in range(1,P+1) if P%p==0 and all(word[t]==word[(t+p)%P] for t in range(P)))
        profiles[name]={'mask':sum(int(c)<<t for t,c in enumerate(word)), 'bits':''.join('1' if c else '0' for c in word),
          'period':period,'height':heights,'drift':heights[-1],'span':max(heights)-min(heights),
          'has00':any(not word[t] and not word[(t+1)%P] for t in range(P)),
          'has11':any(word[t] and word[(t+1)%P] for t in range(P))}
        for cylinder in ['11011','00100','000111','111000']:
            assert all(''.join('1' if word[(t+i)%P] else '0' for i in range(len(cylinder)))!=cylinder for t in range(P))
    for j in range(2,len(names)):
        c,a,u=(bits[names[j-k]] for k in [0,1,2])
        assert all((c[t]^c[(t+1)%P])==(a[t] or u[t]) for t in range(P))
    for j in range(1,len(names)):
        a,c=bits[names[j-1]],bits[names[j]]
        assert all((not a[t] or c[t]!=c[(t+1)%P]) and (c[t]==c[(t+1)%P] or a[t] or a[(t+1)%P]) for t in range(P))
    assert profiles['b']['drift']==0 and profiles['b']['span']<=2 and profiles['b']['period']>8
    for name in ['A','u']:
        assert profiles[name]['has00'] and profiles[name]['has11']
        assert profiles[name]['drift']!=0 or profiles[name]['span']>2
    out['profiles']=profiles;out['independent_literal_check']=True
(root/'one-strip-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
(root/'one-strip-control.smt2').write_text(s.to_smt2(),encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='profiles'}))
