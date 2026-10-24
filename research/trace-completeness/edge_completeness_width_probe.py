"""Finite falsification of a left-edge recovery horizon, not a proof of it."""
import importlib.util
import json
from pathlib import Path
import time
import psutil

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('trace_probe',HERE/'trace_completeness_width_probe.py')
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)

def main():
    start = time.monotonic()
    process = psutil.Process()
    results = []
    stop = None
    for n in range(4,18):
        for c in sorted({0,n//4,n//2,3*n//4,n-1}):
            horizon = 4*n+16
            buckets = {}
            for a in range(1,1 << n):
                if a%4096==1:
                    if (time.monotonic()-start > 100 or process.memory_info().rss > 2*1024**3
                            or psutil.virtual_memory().available < 2*1024**3):
                        stop = 'resource guard; partial finite experiment only'
                        break
                key = probe.trace(a,c,horizon)
                edge = a.bit_length()-1
                previous = buckets.get(key)
                if previous is None:
                    buckets[key] = (edge,a)
                elif previous[0] != edge:
                    stop = 'different-edge finite trace collision'
                    item = {'initial_bit_bound':n,'center_index':c,'horizon':horizon,
                            'unresolved_different_edge_pair':[previous[1],a],
                            'extended_trace_agrees_512':probe.trace(previous[1],c,512)==probe.trace(a,c,512)}
                    results.append(item)
                    break
            if stop:
                break
            keys = sorted(buckets,key=lambda x:int(format(x,f'0{horizon}b')[::-1],2))
            longest = -1
            witnesses = None
            for x,y in zip(keys,keys[1:]):
                if buckets[x][0] == buckets[y][0]:
                    continue
                delta = x ^ y
                common = (delta & -delta).bit_length()-1
                if common > longest:
                    longest = common
                    witnesses = [buckets[x][1],buckets[y][1]]
            item = {'initial_bit_bound':n,'center_index':c,'rows':(1<<n)-1,
                    'horizon':horizon,'trace_classes':len(buckets),
                    'longest_different_edge_common_prefix':longest,
                    'first_edge_distinguishing_horizon':longest+1,
                    'maximal_delay_witness':witnesses,
                    'candidate_2n_plus_2_holds_on_domain':longest+1<=2*n+2}
            results.append(item)
            print(json.dumps(item),flush=True)
        if stop:
            break
    for item in results:
        witness = item.get('maximal_delay_witness')
        if witness:
            a,b = witness
            t = item['longest_different_edge_common_prefix']
            assert probe.trace(a,item['center_index'],t)==probe.trace(b,item['center_index'],t)
            assert probe.trace(a,item['center_index'],t+1)!=probe.trace(b,item['center_index'],t+1)
    report = {'finite_experiment_only':True,'Lean_verified':False,
              'edge_observability_proved':False,'full_problem_solved':False,
              'results':results,'stopped_reason':stop,'seconds':round(time.monotonic()-start,3)}
    (HERE/'edge-completeness-width-probe.json').write_text(json.dumps(report,indent=2)+'\n',
                                                       encoding='utf-8',newline='\n')
    print(json.dumps({'cases':len(results),'stopped_reason':stop,
                      'candidate_counterexamples':[r for r in results if r.get('candidate_2n_plus_2_holds_on_domain') is False],
                      'seconds':report['seconds']}),flush=True)

if __name__=='__main__':
    main()
