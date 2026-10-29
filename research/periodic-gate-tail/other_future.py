from pathlib import Path
import json,time
ROOT=Path(__file__).resolve().parent
start=time.monotonic();q=16;mask=(1<<q)-1;a=mask^1^(1<<6);state=(0,a)
seen={};path=[];limit=100000
while state not in seen and len(path)<limit and time.monotonic()-start<5:
    seen[state]=len(path);path.append(state)
    prev,curr=state;shift=(curr>>1)|((curr&1)<<(q-1));state=(curr,shift^(curr|prev))
complete=state in seen
result={'gate_gap_cycle':[3,5],'gate_period':8,'boundary_time_period':q,'initial_pair':[0,a],'complete':complete,'states_visited':len(path),'state_cap':limit,'seconds_cap':5,'seconds':time.monotonic()-start,'kernel_verified':False}
if complete:
    transient=seen[state];words=[p[1] for p in path[transient:]];P=len(words);maps=[]
    for phase in range(q):
        images=[]
        for first,second in [(0,0),(0,1),(1,0),(1,1)]:
            x,y=first,second
            for w in words:x,y=y,((w>>phase)&1)^(x|y)
            images.append(2*x+y)
        maps.append({'phase':phase,'map':images,'rank':len(set(images))})
    result.update({'transient':transient,'spatial_period':P,'maps':maps,'all_one_block_constant':all(m['rank']==1 for m in maps)})
    (ROOT/'OTHER-FUTURE-WORDS.json').write_text(json.dumps(words)+'\n')
(ROOT/'OTHER-FUTURE.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
