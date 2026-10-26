from pathlib import Path
import json
root=Path(__file__).resolve().parent
data=json.loads((root/'one-strip-control.json').read_bytes())
P=data['clock'];p=data['profiles'];b=p['b']['bits'];A=p['A']['bits'];u=p['u']['bits']
d=[int(b[t])^int(b[(t+1)%P]) for t in range(P)]
starts=[t for t in range(P) if d[t] and not d[(t-1)%P]]
allowed={(1,'1','1'):'1',(3,'011','101'):'3a',(3,'101','111'):'3b',
 (4,'0101','1011'):'4a',(4,'0101','1111'):'4b',(4,'0111','1001'):'4c',(4,'1011','1101'):'4d'}
def bits(word,t,n):return ''.join(word[(t+j)%P] for j in range(n))
def dh(word,t,n):return sum(((-1)**(t+j))*(word[(t+j)%P]=='0') for j in range(n))
rows=[]
for t in starts:
    L=1
    while d[(t+L)%P]:L+=1
    g=1
    while not d[(t+L+g)%P]:g+=1
    aa,uu=bits(A,t,L),bits(u,t,L)
    assert (L,aa,uu) in allowed
    rows.append({'start':t,'active_length':L,'gap':g,'mode':allowed[L,aa,uu],
      'child_segment':bits(b,t,L+g),'A_segment':bits(A,t,L+g),'u_segment':bits(u,t,L+g),
      'signed_increment':{n:dh(p[n]['bits'],t,L+g) for n in ['b','A','u']},
      'A_active_has11':'11' in aa,'u_active_has11':'11' in uu})
assert sum(r['active_length']+r['gap'] for r in rows)==P
assert sum(r['signed_increment']['b'] for r in rows)==0
assert sum(r['signed_increment']['A'] for r in rows)==p['A']['drift']
assert sum(r['signed_increment']['u'] for r in rows)==p['u']['drift']
out={'scope':'One exact fixed cyclic control, no new solver call','rows':rows,'mode_cycle':[r['mode'] for r in rows]}
(root/'mixed-modes.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
