from pathlib import Path
import json,platform,sys
import numpy,numba,psutil
r=Path(__file__).resolve().parent
remote='Rule30-offload' in str(r)
out={'python':platform.python_version(),'numpy':numpy.__version__,'numba':numba.__version__,
     'psutil':psutil.__version__,'machine':'G913' if remote else 'local',
     'available_memory_bytes':psutil.virtual_memory().available}
(r/('versions-remote.json' if remote else 'versions-local.json')).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
