from pathlib import Path
from fractions import Fraction
import hashlib,json,random,re,time
root=Path(__file__).resolve().parent;start=time.monotonic()
ref=Path(r'D:\MWB\Rule30\current-reference-3eca-20261024')
text=(ref/'lean/Ruliology/CellularAutomata/Rule30Ether.lean').read_text(encoding='utf-8')
block=text.split('def wallStates :',1)[1].split('\n]',1)[0]
walls=[(int(p),[int(x.strip()=='true') for x in w.split(',')])
       for p,w in re.findall(r'\((\d+), \[([^\]]+)\]\)',block)]
assert len(walls)==109 and all(len(w)==13 for _,w in walls)
tableblock=text.split('def etherTable :',1)[1].split(']]',1)[0]+']]'
table=[[int(x.strip()=='true') for x in w.split(',')]
       for w in re.findall(r'\[([^\[\]]+)\]',tableblock)]
assert len(table)==7 and all(len(w)==4 for w in table)
wallsets=[{sum(x<<i for i,x in enumerate(w)) for p,w in walls if p==q} for q in range(4)]
patterns=[sum(table[(3+p)%7][q]<<i for i,p in enumerate(range(1,142))) for q in range(4)]
def step(row,t):
    row=((row<<1)^(row|(row>>1)))&~1
    return row|int((t+1)%2==0)
def free_stream(code,n):
    row=code|1;out=[]
    for t in range(2*n-1):
        row=step(row,t)
        if t%2==0:out.append(1^(row>>1&1))
    return out
def scalar_free(code,n):
    row={0}|{p for p in range(1,code.bit_length()) if code>>p&1};out=[]
    for t in range(2*n-1):
        row={p for p in range(1,max(row|{1})+2)
             if int(p-1 in row)^(int(p in row)|int(p+1 in row))}
        if (t+1)%2==0:row.add(0)
        else:out.append(int(1 not in row))
    return out
def normalize(prefix,first):
    prefix=list(prefix)
    while prefix and prefix[-1]==1-first:
        prefix.pop();first^=1
    return prefix,first
def trapped(code,cap=384):
    row=code|1;free=[]
    for T in range(cap+1):
        for phaseoffset in [1,3]:
            phase=(T+phaseoffset)%4
            delta=(row>>1)^patterns[phase]
            matched=(delta&-delta).bit_length()-1 if delta else 141
            k=min(128,matched)
            k -= (k-6)%7
            for k in range(k,5,-7):
                w=(row>>(k+1))&8191
                if w in wallsets[phase]:
                    m=len(free)
                    first=1-table[4][(2*m+1+phaseoffset)%4]
                    prefix,first=normalize(free,first)
                    return {'time':T,'ether_width':k,'phase_offset':phaseoffset,
                            'wall_phase':phase,'wall_code':w,'free_prefix':prefix,'tail_first':first}
        if T==cap:break
        row=step(row,T)
        if T%2==0:free.append(1^(row>>1&1))
    return None
def spatial_cycle(prefix,first,cap=20000):
    m=len(prefix);mu=2*m;width=mu+4;mask=(1<<width)-1
    def f(s):return prefix[s] if s<m else first^((s-m)%2)
    cur=sum((1 if t%2==0 else f(t//2))<<t for t in range(width))
    prev=0;seen={};outputs=[]
    for j in range(cap):
        key=(prev,cur)
        if key in seen:
            begin=seen[key];word=outputs[begin:];black=sum(word);period=len(word)
            return {'entry_depth':begin+1,'period':period,'black':black,
                    'density':str(Fraction(black,period)),
                    'charge_ratio':str(Fraction(3*period,4*black)) if black else 'infinite',
                    'C3_positive_drift':period>4*black,
                    'cycle_bits':''.join(map(str,word)),'entry_previous_hex':hex(prev),
                    'entry_current_hex':hex(cur),'temporal_prefix':mu,'temporal_period':4,'states':len(outputs)}
        seen[key]=j;outputs.append(cur&1)
        shifted=(cur>>1)|(((cur>>mu)&1)<<(width-1))
        prev,cur=cur,(shifted^(cur|prev))&mask
    return {'unknown_at_states':len(outputs)}
controls=0
for code in [0,0x888,0xd6e0,0x72270,*[i<<1 for i in range(32)]]:
    assert free_stream(code,32)==scalar_free(code,32);controls+=32
assert free_stream(0x888,64)==[0,1]+[int(s%2==0) for s in range(2,64)]
ghostpath=Path(r'D:\MWB\Rule30\overnight-20261024\research\agent-experiments\coordinator\20261025-greedy-and-conservation\work\language-filtered-cycles.json')
ghost=json.loads(ghostpath.read_text(encoding='utf-8'))['best']
ghostcycle=spatial_cycle(list(map(int,ghost['prefix_bits'])),ghost['alternating_tail_first_bit'])
assert ghostcycle['density']=='3/14' and ghostcycle['C3_positive_drift']
rng=random.Random(301702)
codes=[0x888,0xd6e0,0x72270]+[i<<1 for i in range(256)]+[1<<p for p in range(1,65)]
codes += [rng.getrandbits(w)<<1 for w in [12,16,24,32,48,64,96] for _ in range(64)]
codes=list(dict.fromkeys(codes));records=[];cache={};best=None;stop=None
outpath=root/'trap-cycles.partial.jsonl'
with outpath.open('w',encoding='utf-8') as log:
    for number,code in enumerate(codes):
        if time.monotonic()-start>240:stop='internal_time_budget';break
        trap=trapped(code)
        rec={'index':number,'initial_right_hex':hex(code),'initial_max_position':code.bit_length()-1,
             'trap':trap}
        if trap:
            key=(tuple(trap['free_prefix']),trap['tail_first'])
            if key not in cache:
                cycle=spatial_cycle(*key)
                cache[key]=cycle
            cycle=cache[key];rec['spatial_cycle']=cycle
            # Independent longer physical replay against the proven-by-trap tail.
            stream=free_stream(code,320)
            m=len(key[0]);expected=list(key[0])+[key[1]^(j%2) for j in range(320-m)]
            assert stream==expected
            if 'period' in cycle:
                if best is None or Fraction(cycle['density'])<Fraction(best['spatial_cycle']['density']):
                    best=rec;print(json.dumps({'new_actual_minimum':rec}),flush=True)
                if cycle['C3_positive_drift']:
                    stop='actual_finite_right_C3_counterexample_candidate'
        records.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
        if stop:break
out={'finite_only':True,'Lean_verified':False,'full_problem_solved':False,
     'controls':{'independent_physical_free_bits':controls,'known_nonrealized_Golden_cycle':ghostcycle},
     'catalog_source_sha256':hashlib.sha256(text.encode('utf-8')).hexdigest(),
     'rng_seed':301702,'requested_codes':len(codes),'processed_codes':len(records),
     'trap_found':sum(x['trap'] is not None for x in records),'unique_complete_streams':len(cache),
     'exact_cycles':sum('period' in x for x in cache.values()),'stop':stop,'best_actual':best,
     'records':records,'elapsed_seconds':time.monotonic()-start,
     'scope':'Trap and spatial cycle are exact candidate certificates; not Lean verified here. Unknown trap/cycle domains are not excluded. Ghost control is not an actual finite right half.'}
(root/'trap-cycles.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['processed_codes','trap_found','unique_complete_streams','exact_cycles','stop','elapsed_seconds']}))
