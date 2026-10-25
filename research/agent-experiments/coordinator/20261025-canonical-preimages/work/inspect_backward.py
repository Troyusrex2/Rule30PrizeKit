from pathlib import Path
from collections import Counter
import json
root=Path(__file__).resolve().parent
d=json.loads((root/'backward-fields.json').read_bytes());rows=d['records']
summary={'late_dimensions':dict(Counter(r['current_dimension'] for r in rows if r['through']==4*r['U'])),
         'all_finite_failures':[{k:r[k] for k in ['U','V','through','current_dimension','all_finite_witness']}
                                for r in rows if not r['all_finite_covers_current']],
         'restricted_failures':[{k:r[k] for k in ['U','V','through','current_dimension','subset_common_witness']}
                                for r in rows if not r['subset_common_covers_current']],
         'all_finite_failures_by_horizon':dict(Counter(r['through'] for r in rows if not r['all_finite_covers_current'])),
         'restricted_failures_by_horizon':dict(Counter(r['through'] for r in rows if not r['subset_common_covers_current']))}
(root/'backward-inspection.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in summary.items() if k not in ['all_finite_failures','restricted_failures']}))
for key in ['all_finite_failures','restricted_failures']:
    print(key,json.dumps(summary[key][:2]))
