"""One fixed-clock local control, not a clock or width sweep.

Finds the exact graph of adjacent period-eight profiles, every individual
profile unsafe, and prunes states without arbitrarily old unsafe ancestry.
This does NOT impose a white spatial boundary.
"""
import json,sys
from pathlib import Path
from collections import deque
root=Path(__file__).parent;P=8;mask=255
def unsafe(p):return any(not(p>>t&1) and not(p>>((t+1)%P)&1) for t in range(P))
mixed='--both-runs' in sys.argv
profiles=[p for p in range(256) if unsafe(p) and (not mixed or unsafe(p^255))]
nodes=[(u,v) for u in profiles for v in profiles];ids={x:i for i,x in enumerate(nodes)}
out=[[] for _ in nodes];inc=[[] for _ in nodes]
for i,(u,v) in enumerate(nodes):
    driver=u|v
    if driver.bit_count()%2:continue
    w=0;bit=0
    for t in range(7):bit^=driver>>t&1;w|=bit<<(t+1)
    for child in [w,w^255]:
        if (v,child) in ids:
            j=ids[v,child];out[i].append(j);inc[j].append(i)
degree=[len(xs) for xs in inc];alive=[True]*len(nodes);queue=deque(i for i,n in enumerate(degree) if n==0)
while queue:
    i=queue.popleft();alive[i]=False
    for j in out[i]:
        degree[j]-=1
        if degree[j]==0:queue.append(j)
group={};collision=None
for i,(u,v) in enumerate(nodes):
    if not alive[i] or u|v==255:continue
    r=u|v
    if r in group and nodes[group[r]][1]!=v:collision=(group[r],i);break
    group[r]=i
report={'period':P,'profiles':len(profiles),'nodes':len(nodes),'edges':sum(map(len,out)),
        'arbitrarily_old_unsafe_core':sum(alive),'collision_found':collision is not None,
        'both00and11_in_every_profile':mixed,'finite_white_ancestry_claimed':False}
if collision:
    witness=[]
    for start in collision:
        path=[start];seen={start:0};i=start
        while True:
            i=next(j for j in inc[i] if alive[j])
            if i in seen:break
            seen[i]=len(path);path.append(i)
        # Backward list plus repeated state encodes every older profile exactly.
        witness.append({'newest_pair':nodes[start],'backward_nodes':[nodes[j] for j in path],
                        'repeat_from':len(path),'repeat_to':seen[i]})
    report['witness']=witness
(root/('ancestry-local-mixed-control.json' if mixed else 'ancestry-local-control.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
