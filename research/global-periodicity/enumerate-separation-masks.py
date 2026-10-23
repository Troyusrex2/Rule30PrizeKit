"""Independent finite enumeration for the Lean separation certificates."""
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('obs',HERE/'trace-observability.py')
obs=importlib.util.module_from_spec(spec)
spec.loader.exec_module(obs)


def edge_mask(horizon,depth):
    center=horizon-1
    high=center+depth
    mask=0
    for row in range(1<<high,1<<(high+1)):
        mask |= 1<<obs.center_trace(row,center,horizon)
    return mask


def main():
    report={'finite_computation_only':True,'cases':[]}
    for h,m,n in [(2,0,1),(3,0,2),(9,1,2),(15,2,3),(3,1,1)]:
        a,b=edge_mask(h,m),edge_mask(h,n)
        result={'horizon':h,'left_depths':[m,n],'trace_counts':[a.bit_count(),b.bit_count()],
                'disjoint':not(a&b),'masks_hex':[hex(a),hex(b)]}
        report['cases'].append(result)
        assert result['disjoint']==(m!=n)
        print(json.dumps({k:v for k,v in result.items() if k!='masks_hex'}),flush=True)
    (HERE/'separation-masks.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')


if __name__=='__main__':
    main()
