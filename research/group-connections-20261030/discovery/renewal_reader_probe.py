from pathlib import Path
import json,time
R=Path(__file__).resolve().parent;start=time.monotonic();N=16384
def rs(r,c):return (r<<1)^(r|(r>>1))^c
r=0;u=[];scalar=[0]*128
for t in range(2*N+1):
    if t%2:u.append(r&1)
    c=int(t%2==0)
    if t<64:
        assert sum(b<<j for j,b in enumerate(scalar))==r
        scalar=[c^(scalar[0]|scalar[1])]+[scalar[j-1]^(scalar[j]|(scalar[j+1] if j+1<128 else 0)) for j in range(1,128)]
    r=rs(r,c)
assert len(u)==N
events=[j for j,b in enumerate(u) if j>=146 and b]
gaps=[b-a for a,b in zip(events,events[1:])]
assert set(gaps)<={3,5}
g=''.join(str((x-3)//2) for x in gaps)
refs={'echo-u':''.join(map(str,u))}
cols={p:[] for p in range(-4,5)};x=1
for t in range(32769):
    for p in cols:cols[p].append(int(t-p>=0 and ((x>>(t-p))&1)))
    x^=(x<<1)|(x<<2)
for p,v in cols.items():refs['seed-column'+str(p)]=''.join(map(str,v))
matches=[];tested=0
for name,ref in refs.items():
    for stride in [1,2,4,8]:
        for residue in range(stride):
            seq=ref[residue::stride]
            for comp in [0,1]:
                target=g[:128] if not comp else g[:128].translate(str.maketrans('01','10'))
                for offset in range(257):
                    tested+=1
                    if seq[offset:offset+128]!=target:continue
                    want=g[:2048] if not comp else g[:2048].translate(str.maketrans('01','10'))
                    matches.append({'reference':name,'stride':stride,'residue':residue,'offset':offset,'complement':comp,'holdout_exact':seq[offset:offset+2048]==want})
    if time.monotonic()-start>30:raise TimeoutError('registered30s')
record={'samples':N,'events_after146':len(events),'gap_bits':len(g),'candidates_tested':tested,'matches':matches,
        'literal_right_half_control_steps':64,'seconds':time.monotonic()-start,
        'scope':'Finite affine-decimation reader only; no inference of automaticity, eventual periodicity, or prize implication.'}
(R/'renewal-reader-result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
