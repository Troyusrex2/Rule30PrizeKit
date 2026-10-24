"""Falsify a finite-support trace-completeness horizon, without claiming proof.

Every final trace bucket is checked pairwise against the early stripe relation.
When all pass, adjacent lexicographic trace keys give the exact longest
common prefix between distinct observed trace classes for that finite domain.
The numerical normalizer is an experimental instrument, not a Lean premise.
"""
import importlib.util
import json
from pathlib import Path
import sys
import time
import psutil

HERE = Path(__file__).resolve().parent
CONTROL = HERE.parent/'normalization-first-meeting/controls.py'
spec = importlib.util.spec_from_file_location('stripe_controls',CONTROL)
controls = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controls)

def phi(a):
    return a ^ ((a << 1) | (a << 2))

def trace(a,c,horizon):
    result = 0
    for t in range(horizon):
        result |= ((a >> (c+t)) & 1) << t
        a = phi(a)
    return result

def main():
    started = time.monotonic()
    results = []
    process = psutil.Process()
    def guard():
        if (time.monotonic()-started > 110 or process.memory_info().rss > 2*1024**3
                or psutil.virtual_memory().available < 2*1024**3):
            raise RuntimeError('Probe resource guard; incomplete, no completeness claim')
    stop = None
    for n in range(4,17):
        for c in sorted({0,n//4,n//2,3*n//4,n-1}):
            horizon = 4*n+16
            buckets = {}
            norms = []
            for a in range(1 << n):
                if a % 4096 == 0:
                    guard()
                key = trace(a,c,horizon)
                buckets.setdefault(key,[]).append(a)
                norms.append((controls.numerical_normalizer(a,c),
                              controls.numerical_normalizer(phi(a),c+1),
                              (a >> c) & 1))
            pairs = 0
            unresolved = None
            for rows in buckets.values():
                for i,a in enumerate(rows):
                    for b in rows[i+1:]:
                        pairs += 1
                        if not (norms[a][0] == norms[b][0]
                                or (norms[a][1]==norms[b][1] and norms[a][2]==norms[b][2])):
                            # A failure of the numeric criterion is rechecked using
                            # the explicit independent stripe grammar and cut.
                            assert not controls.related(a,b,c)
                            assert not controls.related(phi(a),phi(b),c+1)
                            unresolved = [a,b]
                            break
                    if unresolved:
                        break
                if unresolved:
                    break
            keys = sorted(buckets,key=lambda x:int(format(x,f'0{horizon}b')[::-1],2))
            longest = -1
            witnesses = None
            for x,y in zip(keys,keys[1:]):
                delta = x ^ y
                common = (delta & -delta).bit_length()-1
                if common > longest:
                    longest = common
                    witnesses = [buckets[x][0],buckets[y][0]]
            item = {'initial_bit_bound':n,'center_index':c,'rows':1<<n,'horizon':horizon,
                    'trace_classes':len(buckets),'within_bucket_pairs_checked':pairs,
                    'unresolved_equal_trace_pair':unresolved,
                    'longest_common_prefix_distinct_trace_classes':longest,
                    'first_distinguishing_horizon':longest+1,
                    'maximal_delay_witness':witnesses,
                    'candidate_2n_plus_2_holds_on_domain':unresolved is None and longest+1 <= 2*n+2}
            if unresolved:
                item['extended_trace_agrees_512'] = trace(unresolved[0],c,512)==trace(unresolved[1],c,512)
                stop = 'unresolved finite trace collision'
            results.append(item)
            print(json.dumps(item),flush=True)
            if stop:
                break
        if stop:
            break
    report = {'finite_experiment_only':True,'Lean_verified':False,
              'trace_completeness_proved':False,'full_problem_solved':False,
              'results':results,'stopped_reason':stop,'seconds':round(time.monotonic()-started,3)}
    (HERE/'trace-completeness-width-probe.json').write_text(json.dumps(report,indent=2)+'\n',
                                                         encoding='utf-8',newline='\n')

if __name__=='__main__':
    main()
