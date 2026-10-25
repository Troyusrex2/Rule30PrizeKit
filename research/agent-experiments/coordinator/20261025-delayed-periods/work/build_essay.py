from pathlib import Path
import os,subprocess
root=Path(__file__).resolve().parent
engine=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolfram.exe')
env=dict(os.environ,PATH=r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin'+os.pathsep+os.environ['PATH'],
         RULE30PRIZE_KIT=r'D:\MWB\Rule30\current-reference-009005-20261025',
         ELAN_HOME=r'D:\MWB\Rule30\toolchain\leanlink-elan',LEAN_NUM_THREADS='2')
code='PacletDirectoryLoad["D:/MWB/Rule30/leanlink-windows-repair/LeanLink"]; Get["'+(root/'build_essay.wl').as_posix()+'",CharacterEncoding->"UTF-8"]; Quit[]'
cmd=[str(engine),'-noprompt','-run',code]
r=subprocess.run(cmd,cwd=root,env=env,capture_output=True)
(root/'essay-build-wolfram.log').write_bytes(r.stdout+r.stderr)
print((r.stdout+r.stderr).decode('utf-8',errors='replace'),flush=True);r.check_returncode()
