"""Build and fully replay only the new conditional ancestry interface."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
root=Path(__file__).resolve().parent
project=root/'cedar-verifier'
lean=Path(r'D:\MWB\Rule30\toolchain\lean-4.35.0-windows\bin\lean.exe')
name='Rule30RoundTwoAncestryFrontResearch'
checksha='b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905'
assert hashlib.sha256((project/'Check.lean').read_bytes()).hexdigest()==checksha
assert (project/'CedarAncestry.lean').read_bytes()==(root/'snapshots/r30-codex-cedar-20261025T122819Z-e380dd85-v01/CedarAncestry.lean').read_bytes()
shutil.copyfile(root/(name+'.lean'),project/(name+'.lean'))
env=dict(os.environ,LEAN_PATH=str(project/'cedar-build'),PYTHONDONTWRITEBYTECODE='1')
heads=['parent_le_neighbor','least_root_recurrence','canonical_root_recurrence',
       'canonical_left_edge_keeps_root','root_hits_zero_of_nonnegative',
       'problem1_of_least_root_escape']
commands=[[str(lean),'--root='+str(project),'-o',str(project/'cedar-build'/(name+'.olean')),str(project/(name+'.lean'))],
          [str(lean),'--run',str(project/'Check.lean'),name,'--claim','partial']+sum((['--headline',name+'.'+h] for h in heads),[])]
records=[]
for stage,command in zip(['build','check'],commands):
    started=time.monotonic()
    result=subprocess.run(command,cwd=project,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (root/'evidence'/('followup-'+stage+'.log')).write_bytes(result.stdout)
    print(result.stdout.decode('utf-8',errors='replace'),flush=True)
    records.append({'stage':stage,'command':command,'seconds':time.monotonic()-started,'exit_code':result.returncode})
    result.check_returncode()
checked=json.loads(next(s for s in reversed(result.stdout.decode('utf-8').splitlines()) if s.startswith('{')))
assert checked['verdict']=='pass' and checked['replay']['ok'] and not checked['newAxioms']
assert all(h['ok'] for h in checked['headlines'])
report={'source_sha256':hashlib.sha256((root/(name+'.lean')).read_bytes()).hexdigest(),
        'kit_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip(),
        'checker_sha256':checksha,'checker_unchanged':True,'commands':records,'check':checked,
        'scope':'Exact recurrence, persistent least source, crossing and conditional official Problem1 bridge; escape premise UNPROVED',
        'full_problem_solved':False}
(root/'evidence/followup-report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'pass':True,'replay':checked['replay'],'headlines':heads}),flush=True)
