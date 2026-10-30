from pathlib import Path
import json,time

R=Path(__file__).resolve().parent
start=time.monotonic()
results=[]
for gaps,expected in [([5],155),([3,5],325),([3,5,5],None)]:
    period=sum(gaps)
    pos=1
    ones=set()
    for gap in gaps:
        ones.add(pos%period)
        pos+=gap
    q=2*period
    mask=(1 << q)-1
    curr=sum((1 if t%2 else int((t//2)%period not in ones)) << t for t in range(q))
    prev=0
    seen={}
    profiles=[]
    repeated=None
    for k in range(100000):
        if time.monotonic()-start>30:
            break
        pair=(prev,curr)
        if pair in seen:
            repeated=(seen[pair],k-seen[pair])
            break
        seen[pair]=k
        profiles.append(prev)
        shifted=(curr >> 1)|((curr & 1) << (q-1))
        prev,curr=curr,(shifted^(curr|prev)) & mask
    item=dict(gaps=gaps,temporal_period=q,examined_pairs=len(seen),
              status='capped_unknown',expected_control_period=expected)
    if repeated:
        onset,p=repeated
        assert expected is None or p==expected,(gaps,p)
        cycle=profiles[onset:onset+p]
        maps=[]
        nonclosing=[]
        for phase in range(q):
            f=list(range(4))
            for word in cycle:
                bit=word >> phase & 1
                f=[2*(s&1)+(bit ^ int(s!=0)) for s in f]
            cube=[f[f[f[s]]] for s in range(4)]
            maps.append(f)
            if len(set(cube))!=1:
                nonclosing.append(phase)
        item.update(status='exact_periodic_pair_cycle',onset=onset,spatial_period=p,
                    nonsynchronizing_phases=nonclosing,cycle_transfer_maps=maps)
        # Keep the full exact orbit, not only a finite-prefix impression.
        (R/('periodic-cycle-'+''.join(map(str,gaps))+'.json')).write_text(
            json.dumps(dict(gaps=gaps,q=q,onset=onset,cycle=cycle,profiles=profiles))+'\n',encoding='utf-8')
    results.append(item)
out=dict(results=results,seconds=time.monotonic()-start,prize_solved=False,
         all_time_counterexample_proved_in_lean=False)
(R/'periodic-obstruction-result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
