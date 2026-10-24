"""Test a precise finite-prefix proof shape for the driven-right spacing.

At white phases the two-step map is F(x)=rule30_1(rule30_0(x)). We compute
its greatest prefix invariant that is safe against *every* two-bit tail
completion and forbids black observations two cycles apart. Empty results
reject this bounded-prefix proof shape only; they do not refute spacing of
the actual empty-right orbit. Numerical arrays are not Lean certificates.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np


def double_step(x):
    half=(x << 1) ^ (x | (x >> 1))
    return ((half << 1) | 1) ^ (half | (half >> 1))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--widths',nargs='+',type=int,default=[5,6,8,10,12,14,16,18])
    args=ap.parse_args();started=time.monotonic()
    report={'finite_prefix_abstraction_only':True,'spacing_proved':False,'results':[]}
    target=Path(__file__).parent/'right-prefix-safety.json'
    for width in args.widths:
        if not 5<=width<=24:raise ValueError('Use width5..24 for this exhaustive instrument')
        values=np.arange(1 << width,dtype=np.uint64);mask=(1 << width)-1
        bad=((values & 1)!=0) & ((double_step(double_step(values)) & 1)!=0)
        alive=~bad
        successors=[(double_step(values | (tail << width)) & mask).astype(np.uint32)
                    for tail in range(4)]
        rounds=0
        while True:
            nxt=alive.copy()
            for nxt_index in successors:nxt &= alive[nxt_index]
            rounds+=1
            if np.array_equal(nxt,alive):break
            alive=nxt
        actual=1;first_entry=None
        for t in range(257):
            if alive[actual & mask]:first_entry=t;break
            actual=double_step(actual)
        row={'width':width,'states':1 << width,'initially_bad':int(bad.sum()),
             'fixed_point_rounds':rounds,'safe_states':int(alive.sum()),
             'empty_right_first_entry_through_cycle256':first_entry}
        report['results'].append(row);report['seconds']=round(time.monotonic()-started,3)
        target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps(row),flush=True)


if __name__=='__main__':main()
