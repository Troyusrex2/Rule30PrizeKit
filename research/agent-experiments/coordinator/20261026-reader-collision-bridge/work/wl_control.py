from pathlib import Path
import json,subprocess
r=Path(__file__).resolve().parent
exe=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolframscript.exe')
assert exe.is_file()
with (r/'evidence/wolfram-cli.log').open('w',encoding='utf-8') as log:
    z=subprocess.run([str(exe),'-file',str(r/'wolfram_control.wls')],cwd=r,stdout=log,stderr=subprocess.STDOUT)
z.check_returncode()
data=json.loads((r/'wolfram-control.json').read_bytes());assert data['passed']
assert all(x['passed'] for x in data['cases'])
print(json.dumps(data),flush=True)
