"""Falsify the candidate free-variation / reconstructed-weight estimate.

No right-half admissibility restrictions are imposed. SAT models are checked
with an independent ordinary packed forward evolution. UNSAT is not Lean proof.
"""
import argparse
import json
from pathlib import Path
import time

import z3


def search(depth, multiplier, timeout):
    solver = z3.Solver()
    solver.set(timeout=timeout)
    width = depth+1
    previous = old = z3.BitVecVal(0,width)
    free, cells = [], []
    for k in range(depth):
        b = z3.BoolVal(True) if k%2==0 else z3.Bool('f_'+str(k//2))
        if k%2:
            free.append(b)
        scan = old | (previous<<1)
        shift = 1
        while shift < k:
            nxt = z3.BitVec(f'scan_{k}_{shift}',width)
            solver.add(nxt == scan ^ (scan<<shift))
            scan = nxt
            shift *= 2
        mask = (1<<k)-1
        nxt = z3.BitVec('diag_'+str(k+1),width)
        solver.add(nxt == (((scan ^ z3.If(b,z3.BitVecVal(mask,width),z3.BitVecVal(0,width)))&mask)<<1)
                   | z3.If(b,z3.BitVecVal(1,width),z3.BitVecVal(0,width)))
        cells.append(z3.Extract(k,k,nxt)==1)
        previous, old = old, nxt
    changes = [z3.Xor(a,b) for a,b in zip(free,free[1:])]
    solver.add(z3.PbGe([(c,1) for c in changes]+[(z3.Not(c),multiplier) for c in cells],
                      multiplier*depth+1))
    began = time.monotonic()
    status = solver.check()
    result = {'depth':depth,'multiplier':multiplier,'status':str(status),
              'seconds':round(time.monotonic()-began,3)}
    if status==z3.sat:
        model=solver.model()
        f=[int(z3.is_true(model.eval(x,model_completion=True))) for x in free]
        initial=[int(z3.is_true(model.eval(x,model_completion=True))) for x in cells]
        variation=sum(a!=b for a,b in zip(f,f[1:]))
        assert variation>multiplier*sum(initial)
        row=sum(b<<j for j,b in enumerate(initial))
        for t in range(depth):
            assert row&1 == (1 if t%2==0 else f[t//2])
            row=(row>>1)^(row|(row<<1))
        result.update(free_prefix=''.join(map(str,f)),initial_prefix=''.join(map(str,initial)),
                      changes=variation,black_weight=sum(initial),independently_checked=True)
    elif status==z3.unknown:
        result['reason']=solver.reason_unknown()
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cases',nargs='+',default=['49:1','49:2','65:2','97:2','129:2','193:2'])
    ap.add_argument('--timeout-ms',type=int,default=30000)
    args=ap.parse_args()
    report={'finite_experiments_only':True,'unbounded_estimate_proved':False,
            'solver':z3.get_version_string(),'results':[]}
    p=Path(__file__).parent/'variation-weight-sat.json'
    for case in args.cases:
        result=search(*map(int,case.split(':')),args.timeout_ms)
        report['results'].append(result)
        p.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps(result),flush=True)


if __name__=='__main__':main()
