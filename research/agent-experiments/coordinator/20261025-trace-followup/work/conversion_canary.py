from pathlib import Path
import os,subprocess
root=Path(__file__).resolve().parent
engine=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolfram.exe')
env=dict(os.environ,PYTHONUTF8='1',LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
code='$HistoryLength=0; Get["'+(root/'conversion_canary.wl').as_posix()+'",CharacterEncoding->"UTF-8"]; Quit[]'
r=subprocess.run([str(engine),'-noprompt','-run',code],cwd=root,env=env,capture_output=True)
(root/'essay/conversion-canary-wolfram.log').write_bytes(r.stdout+r.stderr)
print((r.stdout+r.stderr).decode('utf-8',errors='replace'),flush=True)
r.check_returncode()
