"""Exact growing right half: search both known ether phases from the empty start.

No right truncation is used. A hit is only a proposed finite trap entry until
kernel certified. Absence in the searched range is not a nonabsorption proof.
"""
import argparse,hashlib,json,random,re,time
from core import BASE,HERE,save

def step(x,t):return ((x<<1)|(1 if t%2==0 else 0))^(x|(x>>1))

def bracket(text,start):
    at=text.index('[',start);depth=0
    for j in range(at,len(text)):
        if text[j]=='[':depth+=1
        elif text[j]==']':
            depth-=1
            if depth==0:return text[at:j+1]
    raise ValueError('Unclosed list')

def patterns():
    source=BASE/'current-reference-3eca-20261024/lean/Ruliology/CellularAutomata/Rule30Ether.lean'
    text=source.read_text(encoding='utf-8')
    etherraw=bracket(text,text.index('def etherTable'))
    ether=[[b=='true' for b in re.findall(r'\btrue\b|\bfalse\b',row)]
           for row in re.findall(r'\[([^\[\]]+)\]',etherraw)]
    assert len(ether)==7 and all(len(row)==4 for row in ether)
    raw=bracket(text,text.index('def wallStates'))
    walls=[set() for _ in range(4)]
    entries=re.findall(r'\((\d+),\s*\[([^\]]*)\]\)',raw)
    assert len(entries)==109
    for phase,row in entries:
        bits=[b=='true' for b in re.findall(r'\btrue\b|\bfalse\b',row)]
        assert len(bits)==13;walls[int(phase)].add(sum(int(b)<<i for i,b in enumerate(bits)))
    low=[sum(int(ether[(3+p)%7][phase])<<(p-1) for p in range(1,7)) for phase in range(4)]
    return low,walls,hashlib.sha256(source.read_bytes()).hexdigest()

def match(x,t,low,walls):
    for offset in (1,3):
        phase=(t+offset)%4
        if x&63==low[phase] and (x>>6)&8191 in walls[phase]:return offset
    return None

def controls(low,walls):
    rng=random.Random(302431);cells=0
    for initial in [0,31,495]+[rng.randrange(4096) for _ in range(9)]:
        x=initial;physical={p:(initial>>(p-1))&1 for p in range(1,14)}
        for t in range(64):
            for p in range(1,max(physical)+1):
                assert (x>>(p-1))&1==physical[p];cells+=1
            physical[0]=1 if t%2==0 else 0;old=physical
            physical={p:(30>>((old.get(p-1,0)<<2)|(old.get(p,0)<<1)|old.get(p+1,0)))&1
                      for p in range(1,max(old)+2)}
            x=step(x,t)
    x=31
    for t in range(4):x=step(x,t)
    assert x==495
    for t in range(4,9):x=step(x,t)
    assert match(x,9,low,walls)==3
    return {'physical_truth_table_cells':cells,'R31_time4_is_R495':True,
            'R31_time9_enters_official_trap':True,'all_passed':True}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--steps',type=int,default=2000000)
    parser.add_argument('--seconds',type=float,default=180);args=parser.parse_args()
    low,walls,sha=patterns();checked=controls(low,walls);start=time.monotonic();x=0;t=0;hit=None
    out={'initial_right_half':0,'driver':'black at even times, white at odd times',
         'searched_phase_offsets':[1,3],'wall_states':109,'official_ether_source_sha256':sha,
         'controls':checked,'Lean_verified':False,'CQ01Empty_proved':False,
         'full_problem_solved':False,'right_truncation':False,'target_steps':args.steps}
    def record(reason):
        raw=x.to_bytes((x.bit_length()+7)//8,'little')
        (HERE/'empty-right-absorption-state.bin').write_bytes(raw)
        out.update({'last_checked_time':t,'state_bit_length':x.bit_length(),
                    'state_sha256':hashlib.sha256(raw).hexdigest(),'seconds':round(time.monotonic()-start,3),
                    'trap_entry':hit,'stop_reason':reason})
        save('empty-right-absorption.json',out)
    while t<=args.steps:
        offset=match(x,t,low,walls)
        if offset is not None:
            hit={'time':t,'phase_offset':offset,'low19':x&((1<<19)-1)};record('candidate_trap_entry');break
        if t%65536==0:
            record('in_progress');print({'checked_through':t,'seconds':out['seconds']},flush=True)
            if time.monotonic()-start>=args.seconds:record('self_time_limit');break
        if t==args.steps:record('target_steps_complete');break
        x=step(x,t);t+=1
    print(out,flush=True)

if __name__=='__main__':main()
