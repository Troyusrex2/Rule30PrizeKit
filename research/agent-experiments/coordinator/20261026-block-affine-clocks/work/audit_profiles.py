"""Rebuild fixed-clock reachability with a literal CA truth-table integrator."""
from pathlib import Path
import json
r=Path(__file__).resolve().parent
probe=r/'diagnostics'
expected=json.loads((probe/'period-front-probe.json').read_bytes())['reports']
def period(x,P):
    for p in [1,2,4,8,16,32,64]:
        if p>P:break
        if all(((x>>t)&1)==((x>>(t%p))&1) for t in range(P)):return p
def integral(u,v,P):
    carry=0;out=0
    for t in range(P):
        out|=carry<<t
        carry=(30>>((carry<<2)|(((u>>t)&1)<<1)|((v>>t)&1)))&1
    return out,carry
reports=[];literal_steps=0
for exp in expected:
    P=exp['clock'];mask=(1<<P)-1;states=[(0,0)];index={(0,0):0};depth=[0];by_or={0:0}
    per=[1];core={0,mask,mask//3,2*(mask//3)};i=0;edges=0;merges=0
    while i<len(states):
        u,v=states[i];w,last=integral(u,v,P);literal_steps+=P
        if not last:
            for z in [w,w^mask]:
                edges+=1;nxt=(v,z)
                if nxt in index:
                    if v not in core or z not in core:merges+=1
                    continue
                j=len(states);index[nxt]=j;states.append(nxt);depth.append(depth[i]+1)
                p=period(z,P);assert per[i]<=p;per.append(p)
                g=v|z
                if g in by_or and g not in [0,mask]:assert states[by_or[g]][1]==z
                else:by_or[g]=j
        i+=1
    assert len(states)==exp['states'] and edges==exp['edges_checked']
    assert max(depth)==exp['maximum_shortest_word_length'] and merges==exp['merges_outside_period_two_core']==0
    reports.append({'clock':P,'states':len(states),'edges':edges,'maximum_shortest_word_length':max(depth),
                    'nonconstant_OR_rigidity_checked':True,'period_drop_absent':True,'noncore_merges':merges})
cex=json.loads((probe/'global-no00.json').read_bytes())['reports'][-1]['OR_one_counterexample']
path=cex['backward_path'];P=8;mask=255
assert cex['u']|cex['v']==mask and (period(cex['u'],P)>2 or period(cex['v'],P)>2)
for parent,child in [(path[j+1],path[j]) for j in range(len(path)-1)]+[(path[cex['repeat_from']],path[-1])]:
    assert child[0]==parent[1]
    w,last=integral(*parent,P);assert last==0 and child[1] in [w,w^mask]
out={'passed':True,'reports':reports,'literal_integrator_steps':literal_steps,
     'infinite_ancestry_cycle_edges_checked':len(path),'white_boundary_counterexample':False,
     'finite_clocks_only':True,'Lean_verified':False,'full_problem_solved':False}
(r/'profile-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out),flush=True)
