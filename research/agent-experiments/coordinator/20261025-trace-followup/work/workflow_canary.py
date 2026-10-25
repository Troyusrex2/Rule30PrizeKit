from pathlib import Path
import json,os,subprocess
root=Path(__file__).resolve().parent
engine=Path(r'C:\Program Files\Wolfram Research\Wolfram Engine\15.0\wolfram.exe')
env=dict(os.environ,PATH=r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin'+os.pathsep+os.environ['PATH'],
         RULE30PRIZE_KIT=r'D:\MWB\Rule30\current-reference-009005-20261025',
         ELAN_HOME=r'D:\MWB\Rule30\toolchain\leanlink-elan',LEAN_NUM_THREADS='1',MIMALLOC_PURGE_DELAY='0')
for stage in ['build','fresh']:
    (root/'essay'/('workflow-canary-'+stage+'.json')).unlink(missing_ok=True)
    code='$HistoryLength=0; stage="'+stage+'"; PacletDirectoryLoad["D:/MWB/Rule30/leanlink-windows-repair/LeanLink"]; Get["'+(root/'workflow_canary.wl').as_posix()+'",CharacterEncoding->"UTF-8"]; Quit[]'
    r=subprocess.run([str(engine),'-noprompt','-run',code],cwd=root,env=env,capture_output=True)
    (root/'essay'/('workflow-canary-'+stage+'-wolfram.log')).write_bytes(r.stdout+r.stderr)
    print((r.stdout+r.stderr).decode('utf-8',errors='replace'),flush=True)
    r.check_returncode()
    record=json.loads((root/'essay'/('workflow-canary-'+stage+'.json')).read_bytes())
    assert record['pass'] and record['completeKernelReplayDeclarations']==1
a=json.loads((root/'essay/workflow-canary-build.json').read_bytes())
b=json.loads((root/'essay/workflow-canary-fresh.json').read_bytes())
assert a['notebookSHA256']==b['notebookSHA256'] and b['separateFreshProcess'] and b['sourceRoundTrip']
print(json.dumps({'pass':True,'build_and_separate_fresh_LeanLink_canary':True,
                  'full_prize_notebook_validated':False}))
