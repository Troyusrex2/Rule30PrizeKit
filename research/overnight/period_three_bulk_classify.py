"""Exact-arithmetic discovery of the bulk coefficient space.

Constructs explicit spatial-coboundary nullvectors and an independent
modular row family. Neither arithmetic result is Lean verified here.
"""
import json
from pathlib import Path
import random
import time

import numpy as np

from period_three_ribbon_graph import Model
from period_three_ribbon_oracle import Oracle
from period_three_bulk_equalities import cycle_equalities


def coboundaries():
    columns = []
    for mode in range(4):
        for phase in range(12):
            for symbol in range(1,4):
                column = np.zeros(768,dtype=np.int64)
                for p in range(12):
                    for pattern in range(16):
                        first = (pattern & 1) | (((pattern >> 2) & 1) << 1)
                        second = ((pattern >> 1) & 1) | (((pattern >> 3) & 1) << 1)
                        column[(mode*12+p)*16+pattern] = int(p == phase and first == symbol)-int((p+1) % 12 == phase and second == symbol)
                columns.append(column)
    # The model omits unmatched all-zero patterns entirely. Their 48
    # formal coefficient columns are unused and are fixed to zero in LPs.
    for pair_phase in range(48):
        column = np.zeros(768,dtype=np.int64)
        column[pair_phase*16] = 1
        columns.append(column)
    return np.stack(columns,axis=1)


def modular_independent_rows(matrix,target,maximum=4096,prime=1000003):
    order = list(range(matrix.shape[0]))
    random.Random(202610240830).shuffle(order)
    pivots, selected = {},[]
    for i in order[:maximum]:
        row = np.asarray(matrix[i].toarray()).ravel().astype(np.int64) % prime
        while True:
            nz = np.flatnonzero(row)
            if not len(nz):
                break
            pivot = int(nz[0])
            value = int(row[pivot])
            if pivot in pivots:
                row = (row-value*pivots[pivot]) % prime
            else:
                row = (row*pow(value,-1,prime)) % prime
                pivots[pivot] = row
                selected.append(i)
                break
        if len(selected) >= target:
            break
    return selected


def main():
    began = time.monotonic()
    model = Model(2,restrict_front=True)
    oracle = Oracle(model)
    full,metadata = cycle_equalities(oracle)
    indices = [(pair_phase*4)*16+pattern for pair_phase in range(48) for pattern in range(16)]
    matrix = full[:,indices].astype(np.int64)
    basis = coboundaries()
    kernel = matrix@basis
    null_ok = bool(np.all(kernel == 0))
    from scipy.sparse import csr_matrix
    null_independent = modular_independent_rows(csr_matrix(basis.T),192,maximum=192)
    selected = modular_independent_rows(matrix,576)
    report = {'Lean_verified':False,'full_problem_claim':False,'exact_integer_and_modular_arithmetic':True,
              'bulk_variables':768,'explicit_coboundary_vectors':144,'unused_zero_pattern_vectors':48,
              'effective_nullity_after_zero_tail_bounds':144,
              'all_explicit_nullvectors_verified':null_ok,'nullvector_modular_rank':len(null_independent),
              'modulus':1000003,'independent_constraint_rows':len(selected),
              'selected_row_indices':selected,'matrix':metadata,
              'classification_discovery_passed':null_ok and len(null_independent) == 192 and len(selected) == 576,
              'kernel_certificate_verified':False,'seconds':round(time.monotonic()-began,3)}
    Path(__file__).with_name('period-three-bulk-classify.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'selected_row_indices'}),flush=True)


if __name__ == '__main__':
    main()
