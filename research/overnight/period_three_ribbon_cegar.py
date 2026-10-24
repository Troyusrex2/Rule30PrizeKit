"""Counterexample-guided discovery of a period-three history ribbon score.

Fits small path constraints, then asks the complete finite history graph for
violating finite words. Neither a bounded oracle answer nor even an exact
graph certificate is a Lean proof of the graph's unbounded coverage.
"""
import argparse
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

from period_three_ribbon_graph import Model, admissible
from period_three_ribbon_oracle import Oracle
from period_three_ribbon_rank_probe import G, good


def constraints(model, words, cycles=()):
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
    for row in cycles:
        append(row,0)
    return csr_matrix((data,cols,ptr),shape=(len(rhs),2*dim)),np.array(rhs,dtype=float)


class IncrementalSolver:
    def __init__(self, model, words, seconds, directory):
        sys.path.insert(0,str(directory.resolve()))
        import highspy
        self.api = highspy
        self.model = model
        self.seconds = seconds
        self.words = set(words)
        self.cycles = set()
        self.h = highspy.Highs()
        for key,value in [('output_flag',False),('threads',2),('solver','simplex'),
                          ('primal_feasibility_tolerance',1e-9),('dual_feasibility_tolerance',1e-9)]:
            assert self.h.setOptionValue(key,value) == highspy.HighsStatus.kOk
        bounds = model.features.bounds()+[(0,None)]*model.dim
        low = np.array([-highspy.kHighsInf if a is None else a for a,b in bounds])
        high = np.array([highspy.kHighsInf if b is None else b for a,b in bounds])
        assert self.h.addVars(2*model.dim,low,high) == highspy.HighsStatus.kOk
        objective = np.r_[np.zeros(model.dim),np.ones(model.dim)]
        assert self.h.changeColsCost(2*model.dim,np.arange(2*model.dim,dtype=np.int32),objective) == highspy.HighsStatus.kOk
        self.add(*constraints(model,words))

    def add(self, matrix, rhs):
        if not len(rhs):
            return
        assert self.h.addRows(len(rhs),np.full(len(rhs),-self.api.kHighsInf),rhs,
            matrix.nnz,matrix.indptr.astype(np.int32),matrix.indices.astype(np.int32),
            matrix.data) == self.api.HighsStatus.kOk

    def solve(self, words, cycles=()):
        fresh = words-self.words
        if fresh:
            matrix,rhs = constraints(self.model,fresh)
            count = 2*len(fresh)
            self.add(matrix[:count],rhs[:count])
            self.words.update(fresh)
        for row in cycles:
            key = tuple(sorted(row.items()))
            if key in self.cycles:
                continue
            indices = np.array([j for j,v in key],dtype=np.int32)
            values = np.array([v for j,v in key],dtype=float)
            matrix = csr_matrix((values,indices,np.array([0,len(key)],dtype=np.int32)),
                                shape=(1,2*self.model.dim))
            self.add(matrix,np.array([0.]))
            self.cycles.add(key)
        self.h.setOptionValue('time_limit',self.h.getRunTime()+self.seconds)
        self.h.run()
        status = self.h.getModelStatus()
        success = status == self.api.HighsModelStatus.kOptimal
        code = 0 if success else (2 if status == self.api.HighsModelStatus.kInfeasible else 1)
        answer = SimpleNamespace(success=success,status=code,message=self.h.modelStatusToString(status),
                                 x=np.array(list(self.h.getSolution().col_value)),
                                 fun=self.h.getObjectiveValue())
        if code == 2:
            ray_status,exists,ray = self.h.getDualRay()
            answer.dual_ray = {str(i):float(v) for i,v in enumerate(ray) if v} if exists else None
        return answer


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--iterations',type=int,default=100)
    ap.add_argument('--radius',type=int,choices=(1,2),default=2)
    ap.add_argument('--max-path',type=int,default=128)
    ap.add_argument('--resume',action='store_true')
    ap.add_argument('--initial-width',type=int,choices=(12,16,20),default=12)
    ap.add_argument('--lp-seconds',type=float,default=10)
    ap.add_argument('--highspy-dir',type=Path)
    ap.add_argument('--learn-cycles',action='store_true')
    ap.add_argument('--seed-report',type=Path)
    ap.add_argument('--extra-words-file',type=Path)
    args = ap.parse_args()
    began = time.monotonic()
    model = Model(args.radius,restrict_front=True)
    checked = model.controls()
    oracle = Oracle(model)
    tag = '-cycles' if args.learn_cycles else ''
    tag += '-incremental' if args.highspy_dir else ''
    path = Path(__file__).with_name('period-three-ribbon-cegar-r'+str(args.radius)+tag+'.json')
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
    if args.seed_report:
        for _ in range(10):
            try:
                seed = json.loads(args.seed_report.read_text())
                break
            except json.JSONDecodeError:
                time.sleep(.05)
        words.update(int(w) for w in seed['training_words'])
    before = len(words)
    for w in range(1 << args.initial_width):
        x,y = G(w),G(G(w))
        if all(good(a) and admissible(a) for a in (w,x,y)):
            words.add(w)
    assert words
    report.setdefault('seed_expansions',[]).append({'width':args.initial_width,'added':len(words)-before})
    report['initial_training_histories'] = report.get('initial_training_histories',len(words))
    report['training_words'] = [str(w) for w in sorted(words)]
    report['solver_backend'] = 'highspy incremental' if args.highspy_dir else 'scipy fresh LP'
    incremental = IncrementalSolver(model,words,args.lp_seconds,args.highspy_dir) if args.highspy_dir else None
    if incremental:
        report['highspy_version'] = incremental.h.version()
    cycle_rows = [{int(j):v for j,v in row.items()} for row in report.get('cycle_rows',[])]
    cycle_keys = {tuple(sorted(row.items())) for row in cycle_rows}
    if args.learn_cycles:
        from period_three_ribbon_cycles import discover, pump_control
    start = len(report['iterations'])
    for iteration in range(start,start+args.iterations):
        if args.extra_words_file:
            try:
                extra = json.loads(args.extra_words_file.read_text())
                words.update(int(w) for w in extra['training_words'])
            except json.JSONDecodeError:
                pass
        if incremental:
            result = incremental.solve(words,cycle_rows)
        else:
            matrix,rhs = constraints(model,words,cycle_rows)
            objective = np.r_[np.zeros(model.dim),np.ones(model.dim)]
            result = linprog(objective,A_ub=matrix,b_ub=rhs,
                             bounds=model.features.bounds()+[(0,None)]*model.dim,
                             method='highs-ds',options={'time_limit':args.lp_seconds})
        record = {'iteration':iteration,'histories':len(words),'status':int(result.status),
                  'message':result.message,'cycle_constraints':len(cycle_rows),'candidate_is_verified_rank':False}
        report['iterations'].append(record)
        if not result.success:
            if incremental and hasattr(result,'dual_ray'):
                report['floating_dual_ray'] = result.dual_ray
            report['stopped_reason'] = 'finite cut LP did not return a candidate'
            path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
            print(json.dumps(record),flush=True)
            break
        coefficients = result.x[:model.dim]
        record.update(L1_norm=float(result.fun),nonzero_coefficients=int(np.count_nonzero(np.abs(coefficients)>1e-9)))
        if args.learn_cycles:
            cuts = discover(oracle,coefficients,rounds=32,maximum=32)
            fresh = []
            for cut in cuts:
                row = {int(j):v for j,v in cut['row'].items()}
                key = tuple(sorted(row.items()))
                if key not in cycle_keys:
                    fresh.append(cut)
                    cycle_rows.append(row)
                    cycle_keys.add(key)
            if fresh:
                record['cycle_cuts_added'] = len(fresh)
                if 'cycle_pumping_control' not in report:
                    report['cycle_pumping_control'] = pump_control(oracle,coefficients,fresh[0])
                report.update(latest_coefficients=coefficients.tolist(),latest_candidate_iteration=iteration,
                              cycle_rows=[{str(j):v for j,v in row.items()} for row in cycle_rows],
                              training_words=[str(w) for w in sorted(words)],seconds=round(time.monotonic()-began,3))
                path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
                print(json.dumps(record),flush=True)
                continue
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
