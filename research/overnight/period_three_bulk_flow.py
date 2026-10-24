"""Exact integer discovery of a balanced bulk flow for ribbon rank gains.

All fourteen-bit input windows induce six bulk Rule 30 steps. Their
uniform flow is projected into the finite history graph. Python checks
are not Lean verification; this is a candidate simplification certificate.
"""
import json
from pathlib import Path
import time

import numpy as np

from period_three_ribbon_graph import Model
from period_three_ribbon_oracle import Oracle


def compute(oracle):
    size = 1 << 14
    rows = [np.arange(size,dtype=np.int64)]
    for _ in range(6):
        x = rows[-1]
        rows.append((x >> 1) ^ (x | (x << 1)))
    first = sum((((rows[t] >> 7) & 1) | (((rows[t] >> 6) & 1) << 1)) << (2*j)
                for j,t in enumerate((5,4,3)))
    second = sum((((rows[t] >> 7) & 1) | (((rows[t] >> 6) & 1) << 1)) << (2*j)
                 for j,t in enumerate((2,1,0)))
    pair = first | (second << 6)
    previous_y = (rows[6] >> 6) & 1
    y = (rows[6] >> 7) & 1
    locations = {(e[0],e[2]):i for i,e in enumerate(oracle.edges)}
    flow = np.zeros(len(oracle.edges),dtype=np.int64)
    missing = []
    for mode in range(8):
        for phase in range(12):
            for k in range(size):
                source = (mode,int(pair[k]),0,phase,3,int(previous_y[k]))
                e = locations.get((source,int(y[k])))
                if e is None:
                    if len(missing) < 8:
                        missing.append({'mode':mode,'phase':phase,'window':k,'source':source,'bit':int(y[k])})
                else:
                    flow[e] += 1
    balance = np.zeros(len(oracle.vertices),dtype=np.int64)
    np.add.at(balance,oracle.source,-flow)
    np.add.at(balance,oracle.target,flow)
    feature_gain = oracle.matrices[0].T@flow
    bulk = np.array([e[0][2] == 0 and e[0][4] == 3 for e in oracle.edges])
    report = {'Lean_verified':False,'full_problem_claim':False,'exact_integer_arithmetic':True,
              'input_windows':size,'head_mode_triples':8,'spatial_phases':12,
              'projected_edge_multiplicity':int(flow.sum()),'edges':len(oracle.edges),
              'positive_edges':int(np.count_nonzero(flow)),'bulk_edges':int(np.count_nonzero(bulk)),
              'all_bulk_edges_positive':bool(np.all(flow[bulk] > 0)),
              'flow_outside_bulk':int(np.count_nonzero(flow[~bulk])),
              'maximum_flow_imbalance':int(np.max(np.abs(balance))),
              'maximum_feature_gain':int(np.max(np.abs(feature_gain))),
              'missing_window_examples':missing,'positive_charge_in_flow':int(flow@oracle.charge),
              'kernel_certificate_verified':False}
    report['AllPassed'] = (not missing and report['all_bulk_edges_positive']
                           and report['flow_outside_bulk'] == 0
                           and report['maximum_flow_imbalance'] == 0
                           and report['maximum_feature_gain'] == 0
                           and report['positive_charge_in_flow'] == 0)
    return flow,report


def main():
    began = time.monotonic()
    model = Model(2,restrict_front=True)
    oracle = Oracle(model)
    flow,report = compute(oracle)
    report['seconds'] = round(time.monotonic()-began,3)
    here = Path(__file__).resolve().parent
    (here/'period-three-bulk-flow.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report),flush=True)


if __name__ == '__main__':
    main()
