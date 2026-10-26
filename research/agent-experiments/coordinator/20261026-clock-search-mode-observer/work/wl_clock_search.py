from pathlib import Path
import subprocess,json
r=Path(__file__).resolve().parent
exe=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolframscript.exe')
with (r/'evidence/wolfram-clock-search-cli.log').open('w',encoding='utf-8') as f:
    z=subprocess.run([str(exe),'-file',str(r/'wolfram_clock_search.wls')],cwd=r,stdout=f,stderr=subprocess.STDOUT)
z.check_returncode();d=json.loads((r/'wolfram-clock-search.json').read_bytes())
assert d['passed'] and d['initial_rows']==1022 and d['anti_clock_cases_with_mask_zero']>0
assert not d['Wolfram_backend_verification'] and not d['full_problem_solved']
print(json.dumps(d))
