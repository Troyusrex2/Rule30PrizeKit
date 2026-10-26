from pathlib import Path
import os,subprocess
root=Path(__file__).resolve().parent
engine=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolfram.exe')
code='$HistoryLength=0; PacletDirectoryLoad["D:/MWB/Rule30/leanlink-windows-repair/LeanLink"]; Get["'+(root/'package_combined_preview.wl').as_posix()+'",CharacterEncoding->"UTF-8"]; Quit[]'
r=subprocess.run([str(engine),'-noprompt','-run',code],cwd=root,env=dict(os.environ,PYTHONUTF8='1'),capture_output=True)
(root/'essay-combined/preview-packaging-wolfram.log').write_bytes(r.stdout+r.stderr)
print((r.stdout+r.stderr).decode('utf-8',errors='replace'),flush=True)
r.check_returncode()
