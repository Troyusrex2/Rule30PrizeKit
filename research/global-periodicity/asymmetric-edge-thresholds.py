"""Find exact bounded observation thresholds for small left-edge pairs."""
import argparse
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('asymmetric',HERE/'asymmetric-edge-search.py')
asymmetric=importlib.util.module_from_spec(spec)
spec.loader.exec_module(asymmetric)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-depth',type=int,default=6)
    parser.add_argument('--upper',type=int,default=16)
    parser.add_argument('--timeout-ms',type=int,default=10000)
    parser.add_argument('--output',default='asymmetric-edge-thresholds.json')
    parser.add_argument('--pairs',nargs='+',help='Optional m:n pairs instead of the full triangle')
    args=parser.parse_args()
    report={'finite_experiment_only':True,'right_prefix_unrestricted':True,'results':[]}
    pairs=[tuple(map(int,p.split(':'))) for p in args.pairs] if args.pairs else [
        (m,n) for n in range(1,args.max_depth+1) for m in range(n)]
    for m,n in pairs:
        checks=[]
        upper=asymmetric.search(m,n,args.upper,args.timeout_ms)
        checks.append(upper)
        result={'left_edges':[-m,-n],'checks':checks}
        if upper['status']=='unsat':
            lo,hi=0,args.upper
            while hi-lo>1:
                mid=(lo+hi)//2
                trial=asymmetric.search(m,n,mid,args.timeout_ms)
                checks.append(trial)
                if trial['status']=='unsat':
                    hi=mid
                elif trial['status']=='sat':
                    lo=mid
                else:
                    break
            result.update(lower_bound=lo+1,upper_bound=hi)
            if hi-lo==1:
                result['minimum_observations']=hi
        report['results'].append(result)
        (HERE/args.output).write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps({k:v for k,v in result.items() if k!='checks'}),flush=True)


if __name__=='__main__':
    main()
