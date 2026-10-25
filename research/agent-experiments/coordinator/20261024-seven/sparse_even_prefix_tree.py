"""Complete golden-prefix tree with a budget on black even coordinates.

There is no beam pruning. Extinction at depth N excludes every golden stream
with at most the budget many black even coordinates among its first N.
Thus it excludes that total budget at arbitrary spatial positions. This is
still not an assertion for every budget. Resource caps retain unknown.
"""
import argparse,json,time
from core import save
from charge_beam_packed import step,controls
from coupled_even_code_probe import decode,forbidden

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--budget',type=int,default=8)
    parser.add_argument('--depth',type=int,default=512);parser.add_argument('--states',type=int,default=250000)
    parser.add_argument('--seconds',type=float,default=180)
    parser.add_argument('--diagnose-merges',action='store_true');args=parser.parse_args()
    filename=f'sparse-even-prefix-budget{args.budget}'+('-merges' if args.diagnose_merges else '')+'.json'
    start=time.monotonic();checked=controls();states=[(0,0,0,0,0,5)];records=[]
    out={'budget':args.budget,'max_depth':args.depth,'state_cap':args.states,'controls':checked,
         'complete_enumeration_not_beam':True,'records':records,'Lean_verified':False,
         'uniform_all_budgets_proved':False,'full_problem_solved':False}
    reason='depth_cap';max_states=1;lastdepth=0;last=[]
    for d in range(args.depth):
        nxt=[];mask=(1<<(2*d+2))-1;last=[]
        for R,Rm,u,word,cost,run in states:
            R1,Rold=step(R,Rm,2*d,1);base,_=step(R1,Rold,2*d+1,0);pred=base>>(2*d+1)&1
            for bit in range(1+(cost<args.budget)):
                s=pred^bit
                if (s==0 and run==0) or (s==1 and run==4):continue
                next_run=(1 if run==5 else run+1) if s else 0
                nxt.append((base^(mask if s else 0),R1,u|(bit<<d),word|(s<<d),cost+bit,next_run))
            if len(nxt)>args.states:reason='state_cap_incomplete_next_level';break
        if reason=='state_cap_incomplete_next_level':break
        if not nxt:
            last=states;states=[];lastdepth=d+1;reason='extinct';break
        states=nxt;lastdepth=d+1;max_states=max(max_states,len(states))
        if d<8:
            expected={u for u in range(1<<(d+1)) if u.bit_count()<=args.budget and forbidden(decode(u,d+1)) is None}
            actual={st[2] for st in states}
            assert actual==expected and len(actual)==len(states)
        hist={str(j):sum(st[4]==j for st in states) for j in range(args.budget+1)}
        row={'depth':d+1,'states':len(states),'cost_histogram':hist}
        if args.diagnose_merges:
            row['distinct_transition_states']=len({(st[0],st[1],st[5]) for st in states})
        records.append(row)
        if (d+1)%8==0:
            save(filename,out)
            print({'depth':d+1,'states':len(states),'minimum_cost':min(st[4] for st in states)},flush=True)
        if time.monotonic()-start>args.seconds:reason='time_budget';break
    # Independently evolve representative complete surviving lanes physically.
    witnesses=last if reason=='extinct' else states
    for st in witnesses[:64]:
        free=[st[3]>>i&1 for i in range((lastdepth-1) if reason=='extinct' else lastdepth)]
        assert decode(st[2],min(len(free),64))==free[:64] and forbidden(free) is None
    out.update({'stop_reason':reason,'extinct':reason=='extinct','last_complete_depth':lastdepth,
                'last_complete_survivors':len(states),'max_complete_states':max_states,
                'last_pre_extinction_inputs_hex':[hex(st[2]) for st in last[:64]],
                'physical_control_lanes':min(len(witnesses),64),
                'seconds':round(time.monotonic()-start,3)})
    save(filename,out)
    print({k:out[k] for k in ['budget','stop_reason','last_complete_depth','max_complete_states','seconds']},flush=True)

if __name__=='__main__':main()
