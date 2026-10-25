"""Exact full temporal-state cycles for explicit eventually alternating streams.
This is a stronger certificate than detecting a repeated output prefix; no
actual finite-right achievability or Lean proof is inferred from it.
"""
from pathlib import Path
import hashlib,importlib.util,json,time,re
root=Path(__file__).resolve().parent
started=time.monotonic()
data=json.loads((root/'wiki-followup.json').read_text())
chosen=next(v for v in data['late_window_counterexamples_or_stress_cases'] if v['finite_density']<2/7-0.005)
prefix=list(map(int,chosen['prefix_bits']));m=len(prefix);tailfirst=1-prefix[-1]
mu=2*m;width=mu+4;mask=(1<<width)-1
def abit(t):return 1 if t%2==0 else (prefix[t//2] if t//2<m else tailfirst^((t//2-m)%2))
cur=sum(abit(t)<<t for t in range(width));prev=0
initial_cur=cur;seen={};states=[];outputs=[]
for depth in range(1,100001):
    key=(prev,cur)
    if key in seen:
        first=seen[key];period=len(states)-first;break
    seen[key]=len(states);states.append(key);outputs.append(cur&1)
    shifted=(cur>>1)|(((cur>>mu)&1)<<(width-1))
    prev,cur=cur,(shifted^(cur|prev))&mask
else:raise RuntimeError('No exact temporal-state cycle found; do not infer an infinite period')

# Independent scalar functional evaluation: no bit-vector representation.
columns=[[0]*(width+64),[abit(t) for t in range(width+64)]]
for d in range(2,33):
    p,c=columns[-2:]
    columns.append([c[t+1]^(c[t]|p[t]) for t in range(len(c)-1)])
for d in range(1,33):
    s=states[d-1]
    assert all(((s[1]>>t)&1)==columns[d][t] for t in range(width))

cycle=outputs[first:first+period];count=sum(cycle)
result={'finite_state_certificate':True,'Lean_verified':False,'prefix_bits':chosen['prefix_bits'],
        'tail_first_bit':tailfirst,'tail':'alternates forever by definition',
        'temporal_preperiod':mu,'temporal_period':4,'temporal_bits_stored_per_column':width,
        'first_periodic_spatial_depth':first+1,'spatial_period':period,'black_per_spatial_period':count,
        'density_numerator':count,'density_denominator':period,
        'cycle_bits':''.join(map(str,cycle)),
        'entry_previous_hex':hex(states[first][0]),'entry_current_hex':hex(states[first][1]),
        'initial_current_hex':hex(initial_cur),'independent_scalar_columns_checked':32,
        'state_count':len(states),'C3_asymptotic_excess_numerator':3*period-12*count,
        'C3_asymptotic_excess_denominator':2*period,
        'scope':'Explicit Golden eventually alternating stream, not established as free R for any finite R. Exact finite recurrence plus periodic-time semantics on paper implies an all-depth Theta cycle.',
        'seconds':time.monotonic()-started}
assert count*7<period*2
(root/'wiki-exact-cycle.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))

# Search for an entry to the *known* official ether-and-wall trap. A prefix
# match alone is only an entry candidate until the official hypotheses replay.
official=Path(r'D:\MWB\Rule30\current-reference-3eca-20261024\lean\Ruliology\CellularAutomata\Rule30Ether.lean')
text=official.read_text(encoding='utf-8')
segment=text[text.index('def wallStates'):text.index('def wallStates')+30000]
entries=re.findall(r'\((\d+),\s*\[([^\]]*)\]\)',segment)
walls=[set() for _ in range(4)]
for phase,row in entries[:109]:
    bits=[x=='true' for x in re.findall(r'\btrue\b|\bfalse\b',row)]
    assert len(bits)==13
    walls[int(phase)].add(sum(int(x)<<j for j,x in enumerate(bits)))
assert sum(map(len,walls))==109
table=['0011','0110','1101','0101','0011','0001','0001']
patterns=[sum(int(table[(3+p)%7][phase])<<(p-1) for p in range(1,222)) for phase in range(4)]
traps=[]
for code in [0x888,0x72270]:
    x=code>>1;hit=None
    for t in range(20001):
        for off in [1,3]:
            phase=(t+off)%4
            for k in range(6,202,7):
                if x&((1<<k)-1)!=patterns[phase]&((1<<k)-1):break
                w=(x>>k)&8191
                if w in walls[phase]:
                    hit={'time':t,'phase_offset':off,'ether_width':k,'wall_code':w,'prefix_code':x&((1<<(k+13))-1)};break
            if hit:break
        if hit:break
        x=(x<<1)^(x|(x>>1))^int(t%2==0)
    traps.append({'right_position_p_at_bit_p_hex':hex(code),'last_time':t,'entry_candidate':hit})
out={'official_source_sha256':hashlib.sha256(official.read_bytes()).hexdigest(),
     'searched_ether_widths':[6,202,7],'searched_through':20000,'finite_only':True,'records':traps}
(root/'wiki-trap-search.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
