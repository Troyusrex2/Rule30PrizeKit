"""Use the exact balanced bulk-flow discovery to simplify score synthesis.

The flow makes every bulk rank-edge inequality tight. Fundamental cycle
equalities then eliminate graph potentials. This remains unverified search
machinery until the finite flow and graph soundness are certified in Lean.
"""
import argparse
from collections import deque
import json
from pathlib import Path
import sys
import time

import numpy as np
from scipy.sparse import csr_matrix,vstack

from period_three_ribbon_graph import Model
from period_three_ribbon_oracle import Oracle
from period_three_ribbon_cegar import constraints
from period_three_bulk_flow import compute


def cycle_equalities(oracle):
    size = 4*12*16
    paths = np.zeros((len(oracle.vertices),size),dtype=np.int16)
    depths = np.zeros(len(oracle.vertices),dtype=np.int32)
    seen = set()
    tree = set()
    def local_gain(edge):
        result = []
        for j,v in oracle.model.gain(edge).items():
            pattern,state = j % 16,j // 16
            assert state % 4 == 0
            result.append(((state // 4)*16+pattern,v))
        return result
    outgoing = [[] for _ in oracle.vertices]
    bulk_edges = []
    for i,e in enumerate(oracle.edges):
        if e[0][2] == 0 and e[0][4] == 3:
            outgoing[oracle.source[i]].append(i)
            bulk_edges.append(i)
    for mode in range(8):
        root = oracle.index[(mode,0,0,0,3,0)]
        assert root not in seen
        seen.add(root)
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for e in outgoing[u]:
                v = int(oracle.target[e])
                if v not in seen:
                    depths[v] = depths[u]+1
                    assert depths[v] < 30000  # Int16 path sums cannot overflow.
                    paths[v] = paths[u]
                    for j,k in local_gain(oracle.edges[e]):
                        paths[v,j] += k
                    seen.add(v)
                    tree.add(e)
                    queue.append(v)
    unique = {}
    maximum = 0
    for e in bulk_edges:
        u,v = int(oracle.source[e]),int(oracle.target[e])
        assert u in seen and v in seen
        row = paths[u].astype(np.int32)-paths[v]
        for j,k in local_gain(oracle.edges[e]):
            row[j] += k
        nonzero = np.flatnonzero(row)
        if not len(nonzero):
            continue
        common = int(np.gcd.reduce(np.abs(row[nonzero])))
        row //= common
        if row[nonzero[0]] < 0:
            row = -row
        maximum = max(maximum,int(np.max(np.abs(row))))
        key = tuple((int(j),int(row[j])) for j in nonzero)
        unique.setdefault(key,None)
    data,cols,ptr = [],[],[0]
    for row in unique:
        for j,v in row:
            pair_phase,pattern = divmod(j,16)
            full = (pair_phase*4)*16+pattern
            cols.append(full)
            data.append(v)
        ptr.append(len(data))
    matrix = csr_matrix((data,cols,ptr),shape=(len(unique),oracle.model.dim),dtype=float)
    return matrix,{'bulk_vertices':len(seen),'bulk_edges':len(bulk_edges),'tree_edges':len(tree),
                   'maximum_tree_path_length':int(depths.max()),
                   'distinct_primitive_cycle_equalities':len(unique),'maximum_integer_coefficient':maximum,
                   'equality_nonzeros':matrix.nnz}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--highspy-dir',type=Path,required=True)
    ap.add_argument('--training',type=Path,required=True)
    ap.add_argument('--seconds',type=float,default=90)
    args = ap.parse_args()
    began = time.monotonic()
    sys.path.insert(0,str(args.highspy_dir.resolve()))
    import highspy
    model = Model(2,restrict_front=True)
    oracle = Oracle(model)
    flow,flow_report = compute(oracle)
    assert flow_report['AllPassed']
    equalities,equality_report = cycle_equalities(oracle)
    print(json.dumps(equality_report),flush=True)
    training = json.loads(args.training.read_text())
    words = {int(w) for w in training['training_words']}
    cycles = [{int(j):v for j,v in row.items()} for row in training.get('cycle_rows',[])]
    full,rhs = constraints(model,words,cycles)
    history_count = 2*len(words)
    inequalities = vstack((full[:history_count,:model.dim],full[history_count+2*model.dim:,:model.dim]),format='csr')
    upper = np.r_[rhs[:history_count],rhs[history_count+2*model.dim:]]
    h = highspy.Highs()
    for k,v in [('output_flag',False),('threads',2),('solver','simplex'),('time_limit',args.seconds),
                ('primal_feasibility_tolerance',1e-9),('dual_feasibility_tolerance',1e-9)]:
        assert h.setOptionValue(k,v) == highspy.HighsStatus.kOk
    bounds = model.features.bounds()
    h.addVars(model.dim,np.array([-highspy.kHighsInf if a is None else a for a,b in bounds]),
              np.array([highspy.kHighsInf if b is None else b for a,b in bounds]))
    def add(matrix,low,high):
        assert h.addRows(matrix.shape[0],low,high,matrix.nnz,matrix.indptr.astype(np.int32),
                         matrix.indices.astype(np.int32),matrix.data.astype(float)) == highspy.HighsStatus.kOk
    add(inequalities,np.full(len(upper),-highspy.kHighsInf),upper)
    add(equalities,np.zeros(equalities.shape[0]),np.zeros(equalities.shape[0]))
    print(json.dumps({'stage':'LP','variables':model.dim,'inequalities':len(upper),
                      'equalities':equalities.shape[0]}),flush=True)
    h.run()
    status = h.getModelStatus()
    report = {'Lean_verified':False,'full_problem_claim':False,'C3w_011_proved':False,
              'flow':flow_report,'equalities':equality_report,'training_histories':len(words),
              'status':h.modelStatusToString(status),'candidate_is_verified_rank':False,
              'exact_LP_refutation':False,'seconds':round(time.monotonic()-began,3)}
    if status == highspy.HighsModelStatus.kOptimal:
        report['floating_coefficients'] = list(h.getSolution().col_value)
    if status == highspy.HighsModelStatus.kInfeasible:
        _,exists,ray = h.getDualRay()
        report['floating_dual_ray'] = {str(i):float(v) for i,v in enumerate(ray) if v} if exists else None
    private = Path('D:/MWB/Rule30/wolfram-local')
    if private.is_dir():
        h.writeModel(str(private/'period-three-bulk-equalities.mps'))
    Path(__file__).with_name('period-three-bulk-equalities.json').write_text(json.dumps(report,indent=2)+'\n',
                                                                         encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('floating_coefficients','floating_dual_ray')}),flush=True)


if __name__ == '__main__':
    main()
