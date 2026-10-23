"""Incremental right-unrestricted edge separation; unknown is never a proof."""
import argparse
import json
from pathlib import Path
import time
import z3


def trace(row,center,horizon):
    result=0
    for t in range(horizon):
        result|=((row>>(center+t))&1)<<t
        row^=(row<<1)|(row<<2)
    return result


def search(m,n,max_horizon,timeout):
    started=time.monotonic()
    center=max_horizon-1
    initial=center+max(m,n)+1
    bits=max(initial,center+max_horizon)
    a,b=z3.BitVecs('a b',initial)
    solver=z3.Solver()
    solver.set(timeout=timeout)
    for row,depth in [(a,m),(b,n)]:
        k=center+depth
        solver.add(z3.Extract(k,k,row)==1,z3.LShR(row,k+1)==0)
    x,y=z3.ZeroExt(bits-initial,a),z3.ZeroExt(bits-initial,b)
    report={'left_edges':[-m,-n],'max_horizon':max_horizon,'checks':[]}
    previous=None
    for t in range(max_horizon):
        solver.add(z3.Extract(center+t,center+t,x)==z3.Extract(center+t,center+t,y))
        status=solver.check()
        report['checks'].append({'horizon':t+1,'status':str(status)})
        if status==z3.unsat:
            report['minimum_observations']=t+1
            report['last_sat_witness']=previous
            break
        if status==z3.unknown:
            report['reason']=solver.reason_unknown()
            report['lower_bound']=t+1
            break
        model=solver.model()
        # Drop cells beyond the current observation cone; they were arbitrary.
        av=model.eval(a).as_long()>>(center-t)
        bv=model.eval(b).as_long()>>(center-t)
        delta=trace(av,t,t+2049)^trace(bv,t,t+2049)
        first=None if not delta else (delta&-delta).bit_length()-1
        assert first is None or first>=t+1
        previous={'rows':[av,bv],'center_index':t,'agrees_length':t+1,
                  'first_difference':first,'verification_horizon':t+2049,
                  'independently_checked':True}
        nx,ny=z3.BitVecs(f'x_{t+1} y_{t+1}',bits)
        solver.add(nx==x^((x<<1)|(x<<2)),ny==y^((y<<1)|(y<<2)))
        x,y=nx,ny
    report['seconds']=round(time.monotonic()-started,3)
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pairs',nargs='+',default=['0:12','0:16','7:8','8:9'])
    parser.add_argument('--max-horizon',type=int,default=64)
    parser.add_argument('--timeout-ms',type=int,default=5000)
    parser.add_argument('--output',default='incremental-asymmetric-search.json')
    args=parser.parse_args()
    report={'finite_solver_evidence_only':True,'right_prefix_unrestricted':True,
            'solver':z3.get_version_string(),'results':[]}
    for pair in args.pairs:
        m,n=map(int,pair.split(':'))
        result=search(m,n,args.max_horizon,args.timeout_ms)
        report['results'].append(result)
        (Path(__file__).parent/args.output).write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps({k:v for k,v in result.items() if k!='checks'}),flush=True)


if __name__=='__main__':
    main()
