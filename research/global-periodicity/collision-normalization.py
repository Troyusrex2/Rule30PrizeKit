"""Test whether finite trace collisions eventually reduce to a stripe tail.

This is a falsification experiment for a possible proof route.  No completeness
claim about infinite traces or about the proposed reduction is made.
"""
import argparse
from collections import defaultdict
import importlib.util
import json
from pathlib import Path
import time

ROOT = Path(__file__).parent
spec = importlib.util.spec_from_file_location('observability', ROOT/'trace-observability.py')
observability = importlib.util.module_from_spec(spec)
spec.loader.exec_module(observability)


def normalize(row, center_index):
    if not row:
        return 0
    low = (row & -row).bit_length()-1
    # At base j, the terminal word is 1, 11, 101, 1011, 10101, ... .
    pattern = 1 << low
    result = row
    for j in range(low, min(center_index,row.bit_length()-1)+1):
        if j > low:
            pattern = (pattern << 1) + (1 if (j-low)%2 else -1)*(1 << low)
        if (row & ((1 << (j+1))-1) == pattern
                and not (row >> (j+1)) & 1):
            result = (row >> j) << j
    return result


def meeting(a,b,width,horizon):
    for t in range(horizon):
        if normalize(a,width+t) == normalize(b,width+t):
            return t
        a,b = observability.phi(a),observability.phi(b)
    return None


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--width',type=int,default=8)
    parser.add_argument('--trace-horizon',type=int,default=128)
    parser.add_argument('--meeting-horizon',type=int,default=256)
    args=parser.parse_args()
    started=time.monotonic()
    for length in range(16):
        stripe=sum(1 << (length-i) for i in range(0,length,2)) | 1
        assert normalize(stripe,length)==1 << length
    # Exhaustive independent finite trace preservation check for the reduction.
    for width in range(6):
        for row in range(1 << (2*width+1)):
            assert observability.center_trace(row,width,128) == observability.center_trace(
                normalize(row,width),width,128)
    groups=defaultdict(list)
    for row in range(1 << (2*args.width+1)):
        groups[observability.center_trace(row,args.width,args.trace_horizon)].append(row)
    pairs=0
    hist=defaultdict(int)
    failures=[]
    for rows in groups.values():
        a=rows[0]
        for b in rows[1:]:
            pairs+=1
            t=meeting(a,b,args.width,args.meeting_horizon)
            if t is None:
                failures.append([a,b])
            else:
                hist[t]+=1
    diagnostics=[]
    for av,bv in failures[:20]:
        a,b=av,bv
        max_bits=0
        first=None
        for t in range(4096):
            delta=a^b
            max_bits=max(max_bits,delta.bit_length())
            if first is None and (delta >> (args.width+t)) & 1:
                first=t
            a,b=observability.phi(a),observability.phi(b)
        diagnostics.append({'rows':[av,bv], 'first_difference':first,
                            'verified_length':4096,'max_differing_bit_count':max_bits,
                            'final_differing_bit_count':(a^b).bit_length()})
    report={'finite_experiment_only':True, 'width':args.width,
            'trace_horizon':args.trace_horizon,'meeting_horizon':args.meeting_horizon,
            'pairs':pairs,'meeting_times':dict(sorted(hist.items())),
            'unresolved_count':len(failures),'unresolved_examples':failures[:20],
            'unresolved_diagnostics':diagnostics,
            'seconds':round(time.monotonic()-started,3)}
    (ROOT/f'collision-normalization-w{args.width}.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report))


if __name__=='__main__':
    main()
