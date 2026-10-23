"""Stress-test edge recovery without assuming a short right half.

Fixed left edges -m and -n, arbitrary cells to their right up to radius H-1.
This realizes every right prefix relevant to H center observations. SAT is
only finite agreement; UNSAT is only bounded solver evidence.
"""
import argparse
import json
from pathlib import Path
import time
import z3


def packed_trace(row, center, horizon):
    result=0
    for t in range(horizon):
        result |= ((row>>(center+t))&1)<<t
        row ^= (row<<1)|(row<<2)
    return result


def search(m,n,horizon,timeout):
    started=time.monotonic()
    right=horizon-1
    initial_bits=right+max(m,n)+1
    bits=max(initial_bits,right+horizon)
    a,b=z3.BitVecs('a b',initial_bits)
    solver=z3.Solver()
    solver.set(timeout=timeout)
    for row,edge in [(a,m),(b,n)]:
        k=right+edge
        solver.add(z3.Extract(k,k,row)==1,z3.LShR(row,k+1)==0)
    x,y=z3.ZeroExt(bits-initial_bits,a),z3.ZeroExt(bits-initial_bits,b)
    for t in range(horizon):
        solver.add(z3.Extract(right+t,right+t,x)==z3.Extract(right+t,right+t,y))
        if t+1<horizon:
            nx,ny=z3.BitVecs(f'x_{t+1} y_{t+1}',bits)
            solver.add(nx==x^((x<<1)|(x<<2)),ny==y^((y<<1)|(y<<2)))
            x,y=nx,ny
    status=solver.check()
    report={'left_edges':[-m,-n],'right_width':right,'horizon':horizon,
            'status':str(status),'seconds':round(time.monotonic()-started,3)}
    if status==z3.sat:
        model=solver.model()
        av,bv=model.eval(a).as_long(),model.eval(b).as_long()
        delta=packed_trace(av,right,horizon+2048)^packed_trace(bv,right,horizon+2048)
        first=None if not delta else (delta&-delta).bit_length()-1
        assert first is None or first>=horizon
        assert av.bit_length()==right+m+1 and bv.bit_length()==right+n+1
        report.update(rows=[av,bv],first_difference=first,
                      verification_horizon=horizon+2048,independently_checked=True)
    elif status==z3.unknown:
        report['reason']=solver.reason_unknown()
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases',nargs='+',default=['0:1:8','0:2:16','0:3:32',
                         '1:2:32','2:3:32','0:4:64','3:4:64','4:5:64'])
    parser.add_argument('--timeout-ms',type=int,default=30000)
    parser.add_argument('--output',default='asymmetric-edge-search.json')
    args=parser.parse_args()
    report={'finite_experiment_only':True,'solver':z3.get_version_string(),'results':[]}
    for case in args.cases:
        result=search(*map(int,case.split(':')),args.timeout_ms)
        report['results'].append(result)
        (Path(__file__).parent/args.output).write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps(result),flush=True)


if __name__=='__main__':
    main()
