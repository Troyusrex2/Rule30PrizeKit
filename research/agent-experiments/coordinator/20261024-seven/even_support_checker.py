"""Bit-parallel decoder with prescribed even input and golden-prefix guards.

Odd initial cells are unrestricted; this is not the kit's bounded-full-width
checker. Numerical success still needs a generic semantic proof and kernel
checks before it establishes a theorem.
"""
import argparse,time,random
from core import save
from coupled_even_code_probe import decode

def pat(m,s):
    block=((1<<(1<<s))-1)<<(1<<s);width=1<<(s+1)
    for _ in range(m-s-1):block|=block<<width;width*=2
    return block

def scan(y,R,Rm):
    out=[];acc=y
    for i,a in enumerate(R):
        acc^=a|(0 if i==0 else Rm[i-1]);out.append(acc)
    return out,acc

def run(m,horizon):
    N=1<<m;ALL=(1<<N)-1;pats=[pat(m,s) for s in range(m)]
    R=[];Rm=[];history=[];alive=ALL;records=[]
    for d in range(horizon):
        old=R;v,_=scan(ALL,R,Rm);R=[ALL]+v;Rm=old
        v,last=scan(0,R,Rm);free=(pats[d] if d<m else 0)^last
        old=R;R=[free]+[free^p for p in v];Rm=old
        bad00=(ALL^free)&(ALL^history[-1]) if history else 0
        bad11111=free
        if len(history)>=4:
            for p in history[-4:]:bad11111&=p
        else:bad11111=0
        oldalive=alive;alive&=ALL^(bad00|bad11111);history.append(free)
        records.append({'free_bits':d+1,'survivors':alive.bit_count()})
        if not alive:
            witness=(oldalive&-oldalive).bit_length()-1
            return history,records,witness
    return history,records,None

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--input-bits',type=int,default=12)
    parser.add_argument('--horizon',type=int,default=128);args=parser.parse_args()
    start=time.monotonic();history,records,witness=run(args.input_bits,args.horizon)
    N=1<<args.input_bits;rng=random.Random(302456)
    cases=list(range(N)) if N<=256 else sorted(set([0,N-1]+[rng.randrange(N) for _ in range(62)]))
    for u in cases:
        s=decode(u,len(history));assert s==[(p>>u)&1 for p in history]
    if witness is not None:
        s=decode(witness,len(history));assert s==[(p>>witness)&1 for p in history]
    out={'prescribed_even_input_bits':args.input_bits,'lanes':N,'records':records,
         'all_lanes_rejected':records[-1]['survivors']==0,'last_surviving_even_input':witness,
         'free_bits_computed':len(history),'scalar_physical_decoder_controls':len(cases),
         'odd_initial_support_unrestricted':True,'Lean_verified':False,
         'uniform_support_theorem_proved':False,'full_problem_solved':False,
         'seconds':round(time.monotonic()-start,3)}
    save(f'even-support-checker-{args.input_bits}.json',out)
    print({k:v for k,v in out.items() if k!='records'},flush=True)

if __name__=='__main__':main()
