from pathlib import Path
from collections import defaultdict
import json
root=Path(__file__).resolve().parent
old=root.parent/'column-reader-20261026T0300'
p=json.loads((old/'invariance-product.json').read_bytes());d=defaultdict(set)
for a,b,_,_ in p['states']:d[a].add(b)
print(json.dumps({k:sorted(v) for k,v in d.items()}))
