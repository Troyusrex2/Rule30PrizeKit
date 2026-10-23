"""Try finite ancestors of exact stripe-tail trace equivalents.

This probes a possible completeness route for finite trace equivalence. It
does not assume that every trace equivalence is obtained by this operation.
The stripe extension is used only with a white cell preceding its anchor.
"""
import argparse
import json
from pathlib import Path
import time


def phi(n):
    return n^((n<<1)|(n<<2))


def finite_inverse(output):
    result=0
    prev=prevprev=0
    for k in range(output.bit_length()+2):
        bit=((output>>k)&1)^(prev|prevprev)
        result |= bit<<k
        prevprev,prev=prev,bit
    if prev or prevprev:
        return None
    assert phi(result)==output
    return result


def trace(row,center,horizon):
    values=[]
    for t in range(horizon):
        k=center+t
        values.append((row>>k)&1 if k>=0 else 0)
        row=phi(row)
    return values


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-cap',type=int,default=2048)
    parser.add_argument('--source',type=int,default=22)
    parser.add_argument('--depths',nargs='+',type=int,default=[1,3,5])
    args=parser.parse_args()
    started=time.monotonic()
    source=args.source
    r=(source&-source).bit_length()-1
    reference=trace(source,0,max(args.depths))
    records=[]
    for depth in args.depths:
        image=source
        for _ in range(depth):
            image=phi(image)
        image >>= r
        # At the anchor, a preceding white cell gives the stripe rewrite.
        assert image&1 and not (image>>1)&1
        accepted=0
        changed=[]
        inverse_failures=0
        initial_trace_failures=0
        stripe=1
        for cap in range(args.max_cap+1):
            if cap:
                stripe=2*stripe+(1 if cap%2 else -1)
            output=(image<<cap)|(stripe^(1<<cap))
            row=output
            for _ in range(depth):
                row=finite_inverse(row)
                if row is None:
                    break
            if row is None:
                inverse_failures+=1
                continue
            center=cap-r
            if trace(row,center,depth)!=reference[:depth]:
                initial_trace_failures+=1
                continue
            accepted+=1
            prefix=(row>>center) if center>=0 else (row<<(-center))
            if prefix!=source:
                changed.append({'cap_length':cap,'left_prefix':prefix,
                                'row':row,'center_bit':center})
            # An executed finite cross-check of each accepted construction.
            assert trace(row,center,depth+128)==trace(source,0,depth+128)
        records.append({'inverse_depth':depth,'cap_lengths':args.max_cap+1,
                        'no_finite_ancestor':inverse_failures,
                        'initial_trace_mismatch':initial_trace_failures,
                        'accepted':accepted,'changed_left_prefix_count':len(changed),
                        'changed_left_prefix_examples':changed[:4]})
    report={'finite_search_only':True,'source':source,'max_cap':args.max_cap,
            'results':records,'seconds':round(time.monotonic()-started,3)}
    (Path(__file__).parent/'finite-preimage-caps.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report),flush=True)


if __name__=='__main__':
    main()
