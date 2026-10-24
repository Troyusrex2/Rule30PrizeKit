"""Find concrete finite history counterexamples to a proposed ribbon score.

Dynamic programming searches all accepted paths up to a stated length. An
exact fixed point additionally yields graph potentials, not a Lean proof.
Every reported counterexample is reconstructed and checked by scalar G.
"""
import argparse
from fractions import Fraction
from math import lcm
import json
from pathlib import Path
import time

import numpy as np
from scipy.sparse import csr_matrix

from period_three_ribbon_graph import Model, admissible
from period_three_ribbon_rank_probe import G, good, inverse_triple


class Oracle:
    def __init__(self, model):
        self.model = model
        self.vertices = sorted(model.vertices)
        self.index = {u:i for i,u in enumerate(self.vertices)}
        self.sources = np.array([self.index[s] for s in model.sources], dtype=np.int32)
        self.ends = np.array([self.index[e] for e in model.ends if e in self.index], dtype=np.int32)
        self.edges = [e for u in self.vertices for e in model.edges[u] if e[1] in self.index]
        self.source = np.array([self.index[e[0]] for e in self.edges], dtype=np.int32)
        self.target = np.array([self.index[e[1]] for e in self.edges], dtype=np.int32)
        self.charge = np.array([int(e[0][4] == 0 and ((e[0][0] >> 1) & 1) !=
                                    ((e[0][0] >> 2) & 1)) for e in self.edges], dtype=np.int64)
        self.matrices = []
        for old_only in (False, True):
            data, cols, ptr = [], [], [0]
            for e in self.edges:
                for j,v in model.gain(e, old_only).items():
                    cols.append(j)
                    data.append(v)
                ptr.append(len(data))
            self.matrices.append(csr_matrix((np.array(data, dtype=np.int64), cols, ptr),
                                            shape=(len(self.edges), model.dim)))

    @staticmethod
    def rationalize(coefficients):
        rational = [Fraction(float(x)).limit_denominator(4096) for x in coefficients]
        if max(abs(float(q)-x) for q,x in zip(rational,coefficients)) > 1e-8:
            return None
        scale = 1
        for q in rational:
            scale = lcm(scale, q.denominator)
            if scale > 10**9:
                return None
        values = [q.numerator*(scale//q.denominator) for q in rational]
        if max(map(abs,values), default=0) > 10**10:
            return None
        return np.array(values,dtype=np.int64),scale

    def reconstruct(self, layers, target, coefficients, kind, integer_coefficients=None, scale=1):
        node = int(target)
        bits = []
        for previous in reversed(layers):
            edge_index = int(previous[node])
            if edge_index < 0:
                continue
            bits.append(self.edges[edge_index][2])
            node = int(self.source[edge_index])
        assert node in self.sources
        bits.reverse()
        y = sum(b << i for i,b in enumerate(bits))
        mode = self.vertices[node][0]
        result = inverse_triple(y,(mode >> 1) & 1,mode & 1)
        assert result is not None
        x,w = result
        assert G(w) == x and G(x) == y and all(good(a) for a in (w,x,y))
        if self.model.restrict_front:
            assert all(admissible(a) for a in (w,x,y))
        score = self.model.features
        used = integer_coefficients if integer_coefficients is not None else coefficients
        vx = sum(int(used[j])*v if integer_coefficients is not None else used[j]*v
                 for j,v in score.features(x,w).items())
        vy = sum(int(used[j])*v if integer_coefficients is not None else used[j]*v
                 for j,v in score.features(y,x).items())
        violation = vy-vx+scale*int((x & 1) != (y & 1)) if kind == 0 else -vx
        assert violation > (0 if integer_coefficients is not None else 1e-7), (violation,kind)
        return {'old':str(w),'current':str(x),'future':str(y),'path_length':len(bits),
                'old_width':w.bit_length(),'old_score':float(vx/scale),'future_score':float(vy/scale),
                'violation':float(violation/scale),'kind':'decrease' if kind == 0 else 'nonnegative',
                'exact_violation_numerator':int(violation) if integer_coefficients is not None else None,
                'exact_violation_denominator':scale if integer_coefficients is not None else None,
                'scalar_reconstruction_passed':True}

    def search(self, coefficients, max_steps=256, seconds=30):
        began = time.monotonic()
        rational = self.rationalize(coefficients)
        exact = rational is not None
        if exact:
            coefs,scale = rational
        else:
            coefs,scale = np.asarray(coefficients,dtype=float),1
        report = {'Lean_verified':False,'full_problem_claim':False,'exact_graph_arithmetic':exact,
                  'graph_certificate_is_Lean_verified':False,'max_path_length':max_steps,
                  'counterexample':None,'objectives':[]}
        for kind,matrix in enumerate(self.matrices):
            costs = matrix@coefs+(self.charge*scale if kind == 0 else 0)
            floor = -(1 << 60) if exact else -np.inf
            distance = np.full(len(self.vertices),floor,dtype=np.int64 if exact else float)
            distance[self.sources] = 0
            layers = []
            fixed = False
            stop = None
            for length in range(1,max_steps+1):
                values = distance[self.source]+costs
                reachable = distance[self.source] != floor
                values[~reachable] = floor
                updated = distance.copy()
                np.maximum.at(updated,self.target,values)
                if exact:
                    choose = reachable & (values == updated[self.target]) & (values > distance[self.target])
                else:
                    choose = reachable & (values >= updated[self.target]-1e-10) & (values > distance[self.target]+1e-10)
                previous = np.full(len(self.vertices),-1,dtype=np.int32)
                previous[self.target[choose]] = np.nonzero(choose)[0]
                layers.append(previous)
                best_end = int(self.ends[np.argmax(updated[self.ends])])
                bound = 0 if exact else 1e-6
                if updated[best_end] > bound:
                    report['counterexample'] = self.reconstruct(layers,best_end,
                        (coefs/scale).tolist(),kind,coefs.tolist() if exact else None,scale)
                    report.update(path_length_examined=length,seconds=round(time.monotonic()-began,3))
                    return report
                if np.array_equal(updated,distance):
                    fixed = True
                    distance = updated
                    break
                distance = updated
                if time.monotonic()-began > seconds:
                    stop = 'time guard'
                    break
            potential_ok = bool(np.all(distance[self.source]+costs <= distance[self.target])
                                and np.all(distance[self.ends] <= 0)
                                and np.all(distance[self.sources] >= 0))
            report['objectives'].append({'kind':kind,'iterations':length,'fixed_point':fixed,
                                         'all_potential_inequalities':potential_ok,
                                         'stopped_reason':stop})
            if exact and fixed and potential_ok:
                report['objectives'][-1]['integer_potential'] = distance.tolist()
            if stop:
                break
        report.update(exact_global_graph_certificate=(exact and len(report['objectives']) == 2
                      and all(x['fixed_point'] and x['all_potential_inequalities'] for x in report['objectives'])),
                      seconds=round(time.monotonic()-began,3))
        return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate',type=Path,required=True)
    ap.add_argument('--max-steps',type=int,default=256)
    args = ap.parse_args()
    data = json.loads(args.candidate.read_text())
    record = data['results'][-1]
    coefficients = record['floating_coefficients']
    model = Model(record['radius'],restrict_front=True)
    checked = model.controls()
    oracle = Oracle(model)
    report = oracle.search(coefficients,args.max_steps)
    report['controls'] = checked
    path = args.candidate.with_name(args.candidate.stem+'-oracle.json')
    path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'objectives'}),flush=True)


if __name__ == '__main__':
    main()
