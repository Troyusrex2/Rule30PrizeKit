"""Find finite rows with different left edges and equal bounded center traces.

Requires z3-solver. SAT witnesses are checked with independent Python integers.
UNSAT is exploratory solver evidence, not a Lean proof. Unknown is not UNSAT.
"""
import argparse
import json
from pathlib import Path
import time
import z3


def trace(row, width, horizon):
    result = 0
    for t in range(horizon):
        result |= ((row >> (width+t)) & 1) << t
        row ^= (row << 1) | (row << 2)
    return result


def search(width, horizon, timeout, fixed_left_edge=None):
    started = time.monotonic()
    initial_bits = 2 * width + 1
    # Phi is triangular: discarded higher bits never influence a lower bit.
    # The largest observed bit is width+horizon-1.
    bits = max(initial_bits, width+horizon)
    a, b = z3.BitVecs('a b', initial_bits)
    solver = z3.Solver()
    solver.set(timeout=timeout)
    solver.add(b != 0)
    solver.add(z3.Or(*[z3.And(z3.Extract(i,i,a) == 1,
                                    z3.LShR(b,i) == 0)
                            for i in range(initial_bits)]))
    if fixed_left_edge is not None:
        bit = width-fixed_left_edge
        assert 0 <= bit < initial_bits
        solver.add(z3.Extract(bit,bit,a) == 1,
                   z3.LShR(a,bit+1) == 0, z3.LShR(b,bit) == 0)
    x, y = z3.ZeroExt(bits-initial_bits,a), z3.ZeroExt(bits-initial_bits,b)
    for t in range(horizon):
        solver.add(z3.Extract(width+t,width+t,x) == z3.Extract(width+t,width+t,y))
        if t+1 < horizon:
            nx, ny = z3.BitVecs(f'x_{t+1} y_{t+1}',bits)
            solver.add(nx == x ^ ((x << 1) | (x << 2)),
                       ny == y ^ ((y << 1) | (y << 2)))
            x, y = nx, ny
    status = solver.check()
    result = {'width': width, 'horizon': horizon, 'status': str(status),
              'fixed_left_edge':fixed_left_edge,
              'seconds': round(time.monotonic()-started,3)}
    if status == z3.sat:
        model = solver.model()
        av, bv = model.eval(a).as_long(), model.eval(b).as_long()
        assert av.bit_length() > bv.bit_length()
        ta, tb = trace(av,width,horizon+4096),trace(bv,width,horizon+4096)
        delta = ta ^ tb
        first = None if delta == 0 else (delta & -delta).bit_length()-1
        assert first is None or first >= horizon
        result.update(rows=[av,bv], left_edges=[width-av.bit_length()+1,
                      None if bv == 0 else width-bv.bit_length()+1],
                      independently_checked=True, first_difference=first,
                      verification_horizon=horizon+4096)
    elif status == z3.unknown:
        result['reason'] = solver.reason_unknown()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases',nargs='+',default=['4:15','6:24','9:28','10:40','12:48','16:64'])
    parser.add_argument('--timeout-ms',type=int,default=30000)
    parser.add_argument('--output',default='symbolic-edge-search.json')
    parser.add_argument('--fixed-left-edge',type=int)
    args = parser.parse_args()
    report = {'finite_experiment_only':True,'solver':z3.get_version_string(),'results':[]}
    for item in args.cases:
        width,horizon = map(int,item.split(':'))
        result = search(width,horizon,args.timeout_ms,args.fixed_left_edge)
        report['results'].append(result)
        (Path(__file__).parent / args.output).write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
        print(json.dumps(result),flush=True)


if __name__ == '__main__':
    main()
