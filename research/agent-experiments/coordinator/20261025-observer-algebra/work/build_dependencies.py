from pathlib import Path
import json,subprocess,time
root=Path(__file__).resolve().parent
ref=Path(r'D:\MWB\Rule30\current-reference-009005-20261025')
lake=Path(r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin\lake.exe')
cmd=[str(lake),'build','Ruliology.CellularAutomata.Rule30FiniteConfigs']
start=time.monotonic();r=subprocess.run(cmd,cwd=ref/'lean',capture_output=True)
(root/'dependencies-build.log').write_bytes(r.stdout+r.stderr)
print((r.stdout+r.stderr).decode('utf-8',errors='replace'));r.check_returncode()
(root/'dependencies-build.json').write_text(json.dumps({'command':cmd,'seconds':time.monotonic()-start,'exit_code':r.returncode})+'\n')
