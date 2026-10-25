"""Explicit finite path involutions, not just path counts or parity assertions.

Retain even path families through zero-disagreement vertices. This matters:
discarding those families without a pairing certificate would hide cancellation.
"""
import json,time
from pathlib import Path
from experiment import step,normalization

ROOT=Path(__file__).resolve().parent

def run(T,P,horizon):
    rows=[{0}]
    for _ in range(T+P):rows.append(step(rows[-1]))
    a=rows[T];b=rows[T+P];d=a^b
    lo,hi=min(d),max(d)
    families={x:{(x,):None} for x in d}
    root_labels={x:x for x in d};left_root=min(d)
    left_family={left_root}
    stats=[];maxpaths=0;maxvertex=0;switches=0
    for t in range(horizon+1):
        residuals={}
        for x,pairs in families.items():
            for path,mate in pairs.items():
                assert path[-1]==x and len(path)==t+1
                if mate is not None:
                    assert mate!=path and pairs[mate]==path
            free=[path for path,mate in pairs.items() if mate is None]
            assert len(free)==int(x in a^b)
            assert len(pairs)%2==int(x in a^b)
            if free:
                residuals[x]=free[0]
                assert free[0][0]==root_labels[x]
        assert set(residuals)==a^b
        labels=[residuals[x][0] for x in sorted(residuals)]
        assert labels==sorted(labels)
        assert {x for x,p in residuals.items() if p[0]==left_root}==left_family
        n=sum(map(len,families.values()))
        maxpaths=max(maxpaths,n)
        maxvertex=max(maxvertex,max(map(len,families.values()),default=0))
        stats.append({'time':t,'total_paths':n,'center_paths':len(families.get(0,{})),
                      'center_residual':list(residuals[0]) if 0 in residuals else None,
                      'root_order':[[x,residuals[x][0]] for x in sorted(residuals)]})
        if t==horizon:break
        nextfamilies={}
        an=step(a);bn=step(b)
        nextlabels={}
        for x in range(lo-t-1,hi+t+2):
            wanted,gauge,active,remainder=normalization(a,b,x)
            switches+=gauge
            weights=[1,int(x+1 not in (b if gauge else a)),int(x not in (a if gauge else b))]
            pairs={};free=[]
            for p,w in zip((x-1,x,x+1),weights):
                if not w:continue
                for path,mate in families.get(p,{}).items():
                    extended=path+(x,)
                    pairs[extended]=None if mate is None else mate+(x,)
                    if mate is None:free.append(extended)
            assert len(free)==len(active)
            residual=None
            if wanted is not None:
                residual=next(path for path in free if path[-2]==wanted)
                nextlabels[x]=root_labels[wanted]
            cancel=[p for p in free if p!=residual]
            assert len(cancel) in (0,2)
            if cancel:
                pairs[cancel[0]]=cancel[1];pairs[cancel[1]]=cancel[0]
            if pairs:nextfamilies[x]=pairs
        left_family=(an^bn)&{x+dx for x in left_family for dx in (-1,0,1)}
        families=nextfamilies;root_labels=nextlabels;a,b=an,bn
    return {'T':T,'P':P,'horizon':horizon,'max_total_paths_one_layer':maxpaths,
            'max_paths_one_vertex':maxvertex,'local_gauge_switches':switches,'layers':stats,
            'all_involutions_fixed_point_free_except_exact_residual':True,
            'all_root_labels_noncrossing':True,'left_root_matches_dilation_recurrence':True}

def main():
    start=time.monotonic()
    runs=[run(T,P,10) for T in range(4) for P in range(1,5)]
    out={'scope':'16 canonical pairs, all paths through time 10; exact tuples and involutions',
         'runs':runs,'seconds':time.monotonic()-start}
    (ROOT/'evidence'/'paths.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'runs':len(runs),'seconds':out['seconds'],
                      'max_paths':max(r['max_total_paths_one_layer'] for r in runs),
                      'max_paths_per_vertex':max(r['max_paths_one_vertex'] for r in runs),
                      'gauge_switches':sum(r['local_gauge_switches'] for r in runs)}))

if __name__=='__main__':main()
