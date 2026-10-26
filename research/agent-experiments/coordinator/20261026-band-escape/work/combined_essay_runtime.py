from pathlib import Path
import datetime as dt,json,os,subprocess
import psutil
root=Path(__file__).resolve().parent

def run(stage):
    assert stage in ['build','fresh']
    available=psutil.virtual_memory().available
    # Keep the existing conservative launch threshold and original guard.
    if available<10500000000:
        record={'state':'not_started_insufficient_memory','stage':stage,
                'available_bytes':available,'required_available_bytes':10500000000,
                'utc':dt.datetime.now(dt.timezone.utc).isoformat(),
                'fresh_notebook_verified':False,'submitted':False}
        (root/'essay-combined'/(stage+'-launch-state.json')).write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
        print(json.dumps(record),flush=True)
        raise SystemExit(3)
    engine=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolfram.exe')
    env=dict(os.environ,PATH=r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin'+os.pathsep+os.environ['PATH'],
             RULE30PRIZE_KIT=r'D:\MWB\Rule30\current-reference-009005-20261025',
             ELAN_HOME=r'D:\MWB\Rule30\toolchain\leanlink-elan',LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
    script=root/('build_combined_essay.wl' if stage=='build' else 'fresh_combined_essay.wl')
    code='$HistoryLength=0; PacletDirectoryLoad["D:/MWB/Rule30/leanlink-windows-repair/LeanLink"]; Get["'+script.as_posix()+'",CharacterEncoding->"UTF-8"]; Quit[]'
    r=subprocess.run([str(engine),'-noprompt','-run',code],cwd=root,env=env,capture_output=True)
    (root/'essay-combined'/(stage+'-wolfram.log')).write_bytes(r.stdout+r.stderr)
    print((r.stdout+r.stderr).decode('utf-8',errors='replace'),flush=True)
    r.check_returncode()
