from pathlib import Path
import os,subprocess
root=Path(__file__).resolve().parent
engine=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolfram.exe')
code='Get["'+(root/'check_exploration.wl').as_posix()+'",CharacterEncoding->"UTF-8"]; Quit[]'
result=subprocess.run([str(engine),'-noprompt','-run',code],cwd=root,env=dict(os.environ,PYTHONUTF8='1'),capture_output=True)
(root/'exploration-wolfram.log').write_bytes(result.stdout+result.stderr)
print((result.stdout+result.stderr).decode('utf-8',errors='replace'),flush=True);result.check_returncode()
