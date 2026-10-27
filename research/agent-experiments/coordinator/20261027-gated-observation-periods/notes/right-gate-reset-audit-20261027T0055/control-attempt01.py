from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent
def D(n):return n^((n>>1)|(n>>2))
def orbit(n,ticks):
    out=[n]
    for _ in range(ticks):out.append(D(out[-1]))
    return out
def pack(bs):return sum(int(b)<<i for i,b in enumerate(bs))
rows={n:orbit(n,16) for n in [2,3,16,33,66]}
assert all((rows[2][t]>>1)==1==(rows[3][t]>>1) and (rows[2][t]^rows[3][t])==1 for t in range(17))
assert rows[2][1]!=rows[2][0] and rows[2][2]==rows[2][0]
assert rows[16][8]==16 and all(rows[16][j]!=16 for j in [1,2,4])
assert all(rows[33][t]>>1==rows[16][t] and rows[66][t]>>1==rows[33][t] for t in range(17))
assert rows[33][8]==33 and rows[66][8]==67 and rows[66][16]==66
a=[n&1 for n in rows[66]];b=[(n>>1)&1 for n in rows[66]];c=[(n>>2)&1 for n in rows[66]];d=[(n>>3)&1 for n in rows[66]];e=[(n>>4)&1 for n in rows[66]]
E=[int(t%2==0) for t in range(17)];q=[b[t]^E[t] for t in range(17)]
ahat=[1^(E[t]&b[t]) for t in range(17)];K=[(1^E[t])&d[t]&(1^c[t]) for t in range(17)]
assert all(not(q[t]&q[t+1]) for t in range(16))
assert all(q[t]^q[t+1]==((1^c[t])&(1^d[t])) for t in range(16))
assert all(ahat[t]^ahat[t+1]^(b[t]|c[t])==K[t] for t in range(16))
g=b[::2];f=c[::2];chi=[d[2*s]|e[2*s] for s in range(9)];kappa=K[1::2]
assert all(g[s+1]==(((1^chi[s])&g[s])^(chi[s]&(1^f[s]))^kappa[s]) for s in range(8))
omitted=[s for s in range(4) if g[s+1]!=(((1^chi[s])&g[s])^(chi[s]&(1^f[s])))]
assert omitted==[1]
gatefails=[t for t in range(8) if not((a[t]|b[t]) if t%2==0 else a[t])]
assert gatefails and gatefails[0]==3
profiles=[234,21,154,149,86,89,101,149,86]
bit=lambda v,t:(v>>(t%8))&1
assert all(bit(profiles[j],t+1)==(bit(profiles[j],t)^(bit(profiles[j+1],t)|bit(profiles[j+2],t))) for j in range(len(profiles)-2) for t in range(8))
assert all((bit(profiles[0],t)|bit(profiles[1],t)) if t%2==0 else bit(profiles[0],t) for t in range(8))
tb=[bit(21,2*s) for s in range(5)];tf=[bit(154,2*s) for s in range(5)];tc=[bit(149,2*s)|bit(86,2*s) for s in range(5)]
tk=[bit(149,2*s+1)&(1^bit(154,2*s+1)) for s in range(4)]
assert tc==[1]*5 and tk==[0]*4
assert all(tb[s+1]==(1^tf[s]) for s in range(4))
assert tb[2]!=tb[0]
r={'scope':'Only the prescribed literal finite-white controls and the inherited boundary-free torus; no census and no Lean claim.',
 'right_translation_control':{'seeds':[2,3],'parent':1,'first_rows':{n:rows[n][:3] for n in [2,3]},'complement_never_erased':True},
 'finite_white_control':{'older_seed':16,'first_extension':33,'twice_extension':66,'rows':{n:rows[n] for n in [16,33,66]},'full_profiles8':{'c':pack(c[:8]),'d':pack(d[:8]),'q':pack(q[:8]),'K':pack(K[:8])},'macro_profiles4':{'g':pack(g[:4]),'f':pack(f[:4]),'chi':pack(chi[:4]),'kappa':pack(kappa[:4])},'forced_reset_pass':True,'unforced_reset_failure_macrotimes':omitted,'first_actual_gate_failure_fulltime':gatefails[0]},
 'inherited_torus':{'credit':'gate-coefficient-audit-20261027T0020 and predecessor-periodicity-paper, reused control','profiles_newest_to_older':profiles,'macro_profiles4':{'g':pack(tb[:4]),'f':pack(tf[:4]),'chi':pack(tc[:4]),'kappa':pack(tk[:4])},'reset_every_macrotime':True,'macro_half_return_fails':True,'finite_white':False}}
(p/'CONTROL.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'result':'PASS','macro_profiles':r['finite_white_control']['macro_profiles4'],'K':r['finite_white_control']['full_profiles8']['K'],'unforced_failure':omitted,'torus':r['inherited_torus']['macro_profiles4']}))
