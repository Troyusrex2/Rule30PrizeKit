"""Probe infinite periodic right completions, with exact merge certificates.

The finite observation of a periodic right half is exact within its causal
cone. A one-step full-image equality is checked on the finite exceptional
prefix and one common tail period. Such a certificate implies equal infinite
traces when the time-zero center cells also agree.
"""
import argparse
from collections import defaultdict
import importlib.util
import json
from math import lcm
from pathlib import Path
import time

HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('observability',HERE/'trace-observability.py')
observability=importlib.util.module_from_spec(spec)
spec.loader.exec_module(observability)


def primitive_words(max_period):
    for period in range(1,max_period+1):
        for n in range(1<<period):
            word=f'{n:0{period}b}'
            if any(period%d==0 and word==word[:d]*(period//d) for d in range(1,period)):
                continue
            yield word


def encode(prefix,word,horizon):
    right=horizon-1
    bits=(word*((right+len(word)-1)//len(word)))[:right]
    return (prefix<<right)|(int(bits,2) if bits else 0)


def cell(config,p):
    prefix,word=config
    return ((prefix>>(-p))&1) if p<=0 else int(word[(p-1)%len(word)])


def image(config,p):
    return cell(config,p-1) ^ (cell(config,p)|cell(config,p+1))


def one_step_merge(a,b):
    # Images are zero left of this bound. For p>=2 both are periodic with
    # a common period lcm(Pa,Pb); checking one complete period is sufficient.
    low=-max(a[0].bit_length(),b[0].bit_length())
    period=lcm(len(a[1]),len(b[1]))
    return all(image(a,p)==image(b,p) for p in range(low,2+period))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-left',type=int,default=8)
    parser.add_argument('--max-period',type=int,default=4)
    parser.add_argument('--horizon',type=int,default=512)
    args=parser.parse_args()
    started=time.monotonic()
    words=list(primitive_words(args.max_period))
    groups=defaultdict(list)
    count=0
    for depth in range(args.max_left+1):
        for free in range(1<<depth):
            prefix=(1<<depth)|free
            for word in words:
                initial=encode(prefix,word,args.horizon)
                trace=observability.center_trace(initial,args.horizon-1,args.horizon)
                groups[trace].append((prefix,word))
                count+=1
    edge_bad=[g for g in groups.values() if len({p.bit_length() for p,w in g})>1]
    left_bad=[g for g in groups.values() if len({p for p,w in g})>1]
    examples=[]
    for group in left_bad[:12]:
        a=group[0]
        b=next(c for c in group if c[0]!=a[0])
        merged=one_step_merge(a,b)
        assert cell(a,0)==cell(b,0)
        delta=observability.center_trace(encode(*a,4096),4095,4096)^observability.center_trace(encode(*b,4096),4095,4096)
        first=None if not delta else (delta&-delta).bit_length()-1
        if merged:
            assert first is None
        examples.append({'configurations':[{'left_prefix':p,'right_period':w} for p,w in [a,b]],
                         'one_step_full_image_merge':merged,'first_difference':first,
                         'verification_horizon':4096})
    report={'finite_search_only':True,'max_left_depth':args.max_left,
            'max_right_period':args.max_period,'horizon':args.horizon,
            'configuration_count':count,'trace_class_count':len(groups),
            'mixed_edge_classes':len(edge_bad),'mixed_left_prefix_classes':len(left_bad),
            'examples':examples,'seconds':round(time.monotonic()-started,3)}
    (HERE/'periodic-right-fibers.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report),flush=True)


if __name__=='__main__':
    main()
