from pathlib import Path
import subprocess,time,json
root=Path(__file__).resolve().parent
ref=Path(r'D:\MWB\Rule30\current-reference-009005-20261025')
lake=Path(r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin\lake.exe')
cmd=[str(lake),'build','Ruliology.CellularAutomata.Rule30ZeroBoundary','Ruliology.CellularAutomata.Rule30StripCertificates']
t=time.monotonic();r=subprocess.run(cmd,cwd=ref/'lean',capture_output=True)
(root/'current-core-build.log').write_bytes(r.stdout+r.stderr)
print((r.stdout+r.stderr).decode('utf-8',errors='replace'),flush=True);r.check_returncode()
(root/'current-core-build.json').write_text(json.dumps({'command':cmd,'cwd':str(ref/'lean'),'seconds':time.monotonic()-t,'exit_code':r.returncode})+'\n')
