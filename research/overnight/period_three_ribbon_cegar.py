"""Counterexample-guided discovery of a period-three history ribbon score.

Fits small path constraints, then asks the complete finite history graph for
violating finite words. Neither a bounded oracle answer nor even an exact
graph certificate is a Lean proof of the graph's unbounded coverage.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from period_three_ribbon_graph import Model, admissible
from period_three_ribbon_oracle import Oracle
from period_three_ribbon_rank_probe import G, good


def constraints(model, words):
    data, cols, ptr, rhs = [], [], [0], []
    def append(row, bound):
        for j,v in row.items():
            if v:
                data.append(float(v))
                cols.append(j)
        ptr.append(len(data))
        rhs.append(bound)
    for w in sorted(words):
        x,y = G(w),G(G(w))
        assert all(good(a) and admissible(a) for a in (w,x,y))
        f,g = model.features.features(x,w),model.features.features(y,x)
        append({j:-v for j,v in f.items()},0)
        delta = dict(g)
        for j,v in f.items():
            delta[j] = delta.get(j,0)-v
        append(delta,-int((x & 1) != (y & 1)))
    dim = model.dim
    for j in range(dim):
        append({j:1,dim+j:-1},0)
        append({j:-1,dim+j:-1},0)
    return csr_matrix((data,cols,ptr),shape=(len(rhs),2*dim)),np.array(rhs,dtype=float)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--iterations',type=int,default=100)
    ap.add_argument('--radius',type=int,choices=(1,2),default=2)
    ap.add_argument('--max-path',type=int,default=128)
    ap.add_argument('--resume',action='store_true')
    ap.add_argument('--initial-width',type=int,choices=(12,16,20),default=12)
    ap.add_argument('--lp-seconds',type=float,default=10)
    args = ap.parse_args()
    began = time.monotonic()
    model = Model(args.radius,restrict_front=True)
    checked = model.controls()
    oracle = Oracle(model)
    path = Path(__file__).with_name('period-three-ribbon-cegar-r'+str(args.radius)+'.json')
    if args.resume:
        report = json.loads(path.read_text())
        assert report['ribbon_radius'] == args.radius and not report['exact_global_graph_certificate']
        assert report.get('stopped_reason') in ('iteration guard',
            'Bounded oracle found no counterexample; no global proof claimed')
        report.pop('stopped_reason')
        words = {int(w) for w in report['training_words']}
    else:
        report = {'Lean_verified':False,'full_problem_claim':False,'C3w_011_proved':False,
                  'controls':checked,'ribbon_radius':args.radius,'iterations':[],
                  'exact_global_graph_certificate':False}
        words = set()
    before = len(words)
    for w in range(1 << args.initial_width):
        x,y = G(w),G(G(w))
        if all(good(a) and admissible(a) for a in (w,x,y)):
            words.add(w)
    assert words
    report.setdefault('seed_expansions',[]).append({'width':args.initial_width,'added':len(words)-before})
    report['initial_training_histories'] = report.get('initial_training_histories',len(words))
    report['training_words'] = [str(w) for w in sorted(words)]
    start = len(report['iterations'])
    for iteration in range(start,start+args.iterations):
        matrix,rhs = constraints(model,words)
        objective = np.r_[np.zeros(model.dim),np.ones(model.dim)]
        result = linprog(objective,A_ub=matrix,b_ub=rhs,
                         bounds=model.features.bounds()+[(0,None)]*model.dim,
                         method='highs-ds',options={'time_limit':args.lp_seconds})
        record = {'iteration':iteration,'histories':len(words),'status':int(result.status),
                  'message':result.message,'candidate_is_verified_rank':False}
        report['iterations'].append(record)
        if not result.success:
            report['stopped_reason'] = 'finite cut LP did not return a candidate'
            path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
            print(json.dumps(record),flush=True)
            break
        coefficients = result.x[:model.dim]
        record.update(L1_norm=float(result.fun),nonzero_coefficients=int(np.count_nonzero(np.abs(coefficients)>1e-9)))
        answer = oracle.search(coefficients,args.max_path,seconds=10)
        report['latest_coefficients'] = coefficients.tolist()
        report['latest_candidate_iteration'] = iteration
        report['latest_oracle'] = answer
        if answer['counterexample'] is not None:
            counter = answer['counterexample']
            w = int(counter['old'])
            record.update(counterexample_old=counter['old'],old_width=counter['old_width'],
                          violation=counter['violation'],kind=counter['kind'])
            if w in words:
                report['stopped_reason'] = 'Numerical or rationalization issue: duplicate violating history'
                path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
                print(json.dumps(record),flush=True)
                break
            words.add(w)
        elif answer.get('exact_global_graph_certificate'):
            report['exact_global_graph_certificate'] = True
            report['stopped_reason'] = 'Exact graph certificate found; graph soundness still requires Lean'
        else:
            report['stopped_reason'] = 'Bounded oracle found no counterexample; no global proof claimed'
        report['training_words'] = [str(w) for w in sorted(words)]
        report['seconds'] = round(time.monotonic()-began,3)
        path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps(record),flush=True)
        if 'stopped_reason' in report:
            break
    else:
        report['stopped_reason'] = 'iteration guard'
        path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')


if __name__ == '__main__':
    main()
