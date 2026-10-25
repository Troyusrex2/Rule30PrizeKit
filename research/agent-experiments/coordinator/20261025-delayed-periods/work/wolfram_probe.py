from pathlib import Path
import os,subprocess
root=Path(__file__).resolve().parent
engine=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolframscript.exe')
env=dict(os.environ,PATH=r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin'+os.pathsep+os.environ['PATH'])
r=subprocess.run([str(engine),'-file',str(root/'wolfram_probe.wl')],cwd=root,env=env,capture_output=True)
print((r.stdout+r.stderr).decode('utf-8',errors='replace'));r.check_returncode()
