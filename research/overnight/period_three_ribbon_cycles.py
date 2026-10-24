"""Discover pumpable cycle constraints for the history ribbon score search.

A positive cycle in a reachable, coaccessible history graph obstructs a
score on all finite accepted words. These are search cuts, not Lean facts.
"""
from collections import deque
import argparse
import json
from math import ceil, gcd
from pathlib import Path
import time

import numpy as np

from period_three_ribbon_graph import Model, admissible
from period_three_ribbon_oracle import Oracle
from period_three_ribbon_rank_probe import G, good, inverse_triple


def predecessor_cycles(oracle, previous):
    done = set()
    for initial in range(len(oracle.vertices)):
        if initial in done:
            continue
        path, local = [], {}
        u = initial
        while u >= 0 and u not in done and u not in local:
            local[u] = len(path)
            path.append(u)
            e = int(previous[u])
            u = int(oracle.source[e]) if e >= 0 else -1
        if u in local:
            # Reverse predecessor order to get a forward directed cycle.
            yield list(reversed([int(previous[v]) for v in path[local[u]:]]))
        done.update(path)


def discover(oracle, coefficients, rounds=64, maximum=64):
    cuts, seen = [], set()
    for kind, matrix in enumerate(oracle.matrices):
        costs = matrix@coefficients+(oracle.charge if kind == 0 else 0)
        distance = np.zeros(len(oracle.vertices))
        previous = np.full(len(oracle.vertices),-1,dtype=np.int32)
        for iteration in range(rounds):
            values = distance[oracle.source]+costs
            updated = distance.copy()
            np.maximum.at(updated,oracle.target,values)
            choose = (values >= updated[oracle.target]-1e-10) & (values > distance[oracle.target]+1e-9)
            previous[oracle.target[choose]] = np.nonzero(choose)[0]
            if np.array_equal(updated,distance):
                break
            distance = updated
            if iteration % 4 != 3:
                continue
            for cycle in predecessor_cycles(oracle,previous):
                cost = float(np.sum(costs[cycle]))
                if cost <= 1e-6:
                    continue
                assert not np.any(oracle.charge[cycle])
                row = {}
                for e in cycle:
                    for j,v in oracle.model.gain(oracle.edges[e],old_only=bool(kind)).items():
                        row[j] = row.get(j,0)+v
                row = {j:v for j,v in row.items() if v}
                assert row
                common = 0
                for v in row.values():
                    common = gcd(common,abs(v))
                row = {j:v//common for j,v in row.items()}
                key = tuple(sorted(row.items()))
                if key in seen:
                    continue
                seen.add(key)
                assert sum(coefficients[j]*v for j,v in row.items()) > 1e-7
                cuts.append({'kind':kind,'row':{str(j):v for j,v in row.items()},
                             'edge_indices':cycle,'length':len(cycle),'floating_cycle_cost':cost,
                             'cycle_states':[list(oracle.edges[e][0]) for e in cycle]})
                if len(cuts) >= maximum:
                    return cuts
    return cuts


def pump_control(oracle, coefficients, cut, max_length=10000):
    n = len(oracle.vertices)
    outgoing, incoming = [[] for _ in range(n)], [[] for _ in range(n)]
    for e,(u,v) in enumerate(zip(oracle.source,oracle.target)):
        outgoing[u].append(e)
        incoming[v].append(e)
    parents = {int(s):None for s in oracle.sources}
    queue = deque(parents)
    while queue:
        u = queue.popleft()
        for e in outgoing[u]:
            v = int(oracle.target[e])
            if v not in parents:
                parents[v] = e
                queue.append(v)
    next_edge = {int(s):None for s in oracle.ends}
    queue = deque(next_edge)
    while queue:
        v = queue.popleft()
        for e in incoming[v]:
            u = int(oracle.source[e])
            if u not in next_edge:
                next_edge[u] = e
                queue.append(u)
    cycle = cut['edge_indices']
    anchor = int(oracle.source[cycle[0]])
    assert int(oracle.target[cycle[-1]]) == anchor
    assert all(int(oracle.target[a]) == int(oracle.source[b]) for a,b in zip(cycle,cycle[1:]))
    prefix, suffix = [], []
    u = anchor
    while parents[u] is not None:
        e = parents[u]
        prefix.append(e)
        u = int(oracle.source[e])
    source = u
    prefix.reverse()
    u = anchor
    while next_edge[u] is not None:
        e = next_edge[u]
        suffix.append(e)
        u = int(oracle.target[e])
    kind = cut['kind']
    costs = oracle.matrices[kind]@coefficients+(oracle.charge if kind == 0 else 0)
    fixed = float(np.sum(costs[prefix])+np.sum(costs[suffix]))
    repeats = max(1,ceil((1-fixed)/cut['floating_cycle_cost']))
    length = len(prefix)+repeats*len(cycle)+len(suffix)
    if length > max_length:
        return {'scalar_control_performed':False,'required_path_length':length}
    path = prefix+cycle*repeats+suffix
    y = sum(oracle.edges[e][2] << i for i,e in enumerate(path))
    mode = oracle.vertices[source][0]
    result = inverse_triple(y,(mode >> 1) & 1,mode & 1)
    assert result is not None
    x,w = result
    assert G(w) == x and G(x) == y and all(good(a) and admissible(a) for a in (w,x,y))
    features = oracle.model.features
    vx = sum(coefficients[j]*v for j,v in features.features(x,w).items())
    vy = sum(coefficients[j]*v for j,v in features.features(y,x).items())
    violation = vy-vx+int((x & 1) != (y & 1)) if kind == 0 else -vx
    assert violation > 1e-6
    return {'scalar_control_performed':True,'AllPassed':True,'path_length':length,
            'cycle_repetitions':repeats,'old_width':w.bit_length(),'violation':float(violation)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate',type=Path,required=True)
    ap.add_argument('--rounds',type=int,default=64)
    args = ap.parse_args()
    for _ in range(10):
        try:
            source = json.loads(args.candidate.read_text())
            break
        except json.JSONDecodeError:
            time.sleep(.05)
    coefficients = np.asarray(source['latest_coefficients'])
    model = Model(source['ribbon_radius'],restrict_front=True)
    oracle = Oracle(model)
    cuts = discover(oracle,coefficients,args.rounds)
    report = {'Lean_verified':False,'full_problem_claim':False,
              'candidate_iteration':source.get('latest_candidate_iteration'),
              'tested_coefficients':coefficients.tolist(),
              'search_constraints_only':True,'positive_cycles':len(cuts),'cuts':cuts}
    if cuts:
        report['pumped_finite_control'] = pump_control(oracle,coefficients,cuts[0])
    path = args.candidate.with_name(args.candidate.stem+'-cycles.json')
    path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('cuts','tested_coefficients')}),flush=True)


if __name__ == '__main__':
    main()
