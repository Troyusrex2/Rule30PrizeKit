from pathlib import Path
import json
p=Path(r'D:\MWB\Rule30\wolfram-local\agent-seven-20261024\column-reader-20261026T0300\learned-reader.json')
d=json.loads(p.read_bytes())['dfa']
for i,row in enumerate(d['transitions']):print(i, 'accept' if i in d['accepting'] else 'reject',d['representatives'][i],row)
print('distinguishers',d['distinguishers'])
