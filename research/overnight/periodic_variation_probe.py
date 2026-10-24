"""Exact finite-state cycles for periodic free bits; not a Lean proof.

When the boundary has temporal period H, every reconstructed temporal column
has that period. Columns are H-bit words, so adjacent columns form a finite
deterministic state. A detected state repetition certifies a spatial cycle by
ordinary integer computation. Any universal consequence still needs proof.
"""
import argparse
import json
from pathlib import Path
import time


def boundary(word, period):
    return sum(1 << j for j in range(0,2*period,2)) | sum(
        ((word >> j)&1) << (2*j+1) for j in range(period))


def rotate(value, width):
    return (value >> 1) | ((value & 1) << (width-1))


def cycle(word, period, cap):
    width=2*period
    a,b=0,boundary(word,period)
    seen={}; out=[]
    while len(out)<cap:
        if (a,b) in seen:
            start=seen[(a,b)]; length=len(out)-start
            ones=sum(out[start:]); changes=sum(
                ((word>>j)&1)!=((word>>((j+1)%period))&1) for j in range(period))
            # Variation per n is changes/period; weight per 2n is 2*ones/length.
            return {'word':word,'period':period,'transient':start,'cycle':length,
                    'cycle_weight':ones,'free_changes_per_period':changes,
                    'asymptotic_ratio':changes*length/(2*period*ones) if ones else None,
                    'spatial_prefix':out[:min(128,len(out))]}
        seen[(a,b)]=len(out);out.append(b&1)
        a,b=b,rotate(b,width)^(b|a)
    return None


def ordinary_control(word,period,depth=128):
    width=2*period;a,b=0,boundary(word,period); initial=0
    for k in range(depth):
        initial|=(b&1)<<k
        a,b=b,rotate(b,width)^(b|a)
    for t in range(depth):
        expect=1 if t%2==0 else (word>>((t//2)%period))&1
        assert initial&1==expect
        initial=(initial>>1)^(initial|(initial<<1))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-period',type=int,default=12)
    ap.add_argument('--cap',type=int,default=100000)
    ap.add_argument('--seconds',type=int,default=300)
    args=ap.parse_args(); started=time.monotonic()
    report={'finite_computation_only':True,'unbounded_estimate_proved':False,
            'unbounded_estimate_refuted_in_Lean':False,'periods':[],
            'max_states_per_word':args.cap,'best':None}
    target=Path(__file__).parent/'periodic-variation-probe.json'
    stop=False
    for p in range(1,args.max_period+1):
        done=unknown=0; best=None
        for word in range(1<<p):
            if time.monotonic()-started>args.seconds:
                stop=True;break
            got=cycle(word,p,args.cap)
            if got is None:unknown+=1;continue
            done+=1
            assert got['cycle_weight']>0, 'Unexpected eventually white row; investigate, do not claim a proof'
            if best is None or got['asymptotic_ratio']>best['asymptotic_ratio']:
                best=got
            if report['best'] is None or got['asymptotic_ratio']>report['best']['asymptotic_ratio']:
                ordinary_control(word,p)
                report['best']=got
        row={'period':p,'cycles_found':done,'cap_reached':unknown,'all_words_tested':done+unknown==1<<p,
             'best':best}
        report['periods'].append(row);report['seconds']=round(time.monotonic()-started,3)
        target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps({k:v for k,v in row.items() if k!='best'}|{'best':None if best is None else
              {k:v for k,v in best.items() if k!='spatial_prefix'}}),flush=True)
        if stop:break


if __name__=='__main__':main()
