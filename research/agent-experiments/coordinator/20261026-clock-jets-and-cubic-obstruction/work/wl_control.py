from pathlib import Path
import subprocess,json
r=Path(__file__).resolve().parent
exe=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolframscript.exe')
with (r/'evidence/wolfram-cli.log').open('w',encoding='utf-8') as log:
    z=subprocess.run([str(exe),'-file',str(r/'wolfram_control.wls')],cwd=r,stdout=log,stderr=subprocess.STDOUT)
z.check_returncode();d=json.loads((r/'wolfram-control.json').read_bytes())
assert d['passed'] and d['initial_rows']==1022 and d['plateau_flag_cases']>0 and d['double_flag_cases']>0
print(json.dumps(d),flush=True)
