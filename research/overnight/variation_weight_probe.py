"""Exact finite falsification of a possible unbounded variation/weight estimate.

If some fixed C bounded free-bit changes by C times reconstructed prefix weight
at every depth, finite support would force eventual constancy of the free bits.
This experiment tests small cones; it does not assert that estimate or Q01.
"""
import argparse
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tables', HERE/'forced_row_identities.py')
tables = importlib.util.module_from_spec(sp)
sp.loader.exec_module(tables)


def add(planes, bits):
    out = planes.copy()
    for j in range(len(out)):
        old = out[j]
        out[j] ^= bits
        bits &= old
    if bits:
        out.append(bits)
    return out


def greater(a, b, all_bits):
    equal, gt = all_bits, 0
    for j in reversed(range(max(len(a), len(b)))):
        av = a[j] if j < len(a) else 0
        bv = b[j] if j < len(b) else 0
        gt |= equal & av & (bv ^ all_bits)
        equal &= (av ^ bv) ^ all_bits
    return gt


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--free-bits', type=int, default=22)
    args = ap.parse_args()
    rows, all_bits, free = tables.tables(args.free_bits)
    changes = []
    for a, b in zip(free, free[1:]):
        changes = add(changes, a ^ b)
    report = {'finite_truth_tables_only': True, 'free_bits':args.free_bits,
              'depth':len(rows), 'unbounded_estimate_proved':False, 'results':[]}
    for c in [1,2,3,4]:
        weighted = []
        for row in rows:
            for _ in range(c):
                weighted = add(weighted, row)
        bad = greater(changes, weighted, all_bits)
        result = {'multiplier':c,'counterexample_exists':bool(bad)}
        if bad:
            assignment = (bad & -bad).bit_length()-1
            f = [(assignment >> j)&1 for j in range(args.free_bits)]
            initial = [(row >> assignment)&1 for row in rows]
            variation = sum(a!=b for a,b in zip(f,f[1:]))
            assert variation > c*sum(initial)
            packed = sum(bit<<j for j,bit in enumerate(initial))
            assert tables.direct(packed,len(rows)) == [1 if t%2==0 else f[t//2]
                                                       for t in range(len(rows))]
            result.update(free_prefix=''.join(map(str,f)),
                          initial_prefix=''.join(map(str,initial)),
                          changes=variation,black_weight=sum(initial),independently_checked=True)
        report['results'].append(result)
    (HERE/'variation-weight-probe.json').write_text(json.dumps(report,indent=2)+'\n',
                                                   encoding='utf-8',newline='\n')
    print(json.dumps(report))


if __name__=='__main__':
    main()
